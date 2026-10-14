{-# LANGUAGE OverloadedStrings #-}

{- | A GHC session for the drivers of "Data.CFTA.GHC.Fits": the benchmark and
the tests. A hole-fit plugin does not need it, because it already runs in
GHC's typechecker.

One session runs for the whole process. Its interactive context has the
imports in scope, as GHCi does. 'fitsForSignature' is the thin wrapper that
a driver needs: it runs the typechecker in the context, skolemises a
signature into a hole, and calls 'streamFits' with the signature's arguments
as required candidates.
-}
module Data.CFTA.GHC.Session (
    -- * Sessions
    Session,
    withSession,
    withSessionPackages,

    -- * Candidates
    Import (..),
    candidatesOf,

    -- * Types
    typeOfExpression,
    accepts,
    declare,

    -- * Fits
    fitsForSignature,
    inSignatureHole,
    inTypechecker,
) where

import Control.Monad (forM, void)
import Control.Monad.IO.Class (liftIO)
import Data.Maybe (isJust)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import System.Environment (lookupEnv)
import System.Process (readProcess)

import Data.CFTA.GHC.Fits (Candidate (..), Fit, Options, Statistics, TypedHole, candidateFromId, holeFor, streamFits)
import GHC (
    Ghc,
    InteractiveImport (IIDecl),
    TcRnExprMode (TM_Inst),
    TyThing (AConLike, AnId),
    exprType,
    findModule,
    getModuleInfo,
    getSession,
    getSessionDynFlags,
    lookupName,
    mkModuleName,
    modInfoExports,
    parseDynamicFlags,
    parseImportDecl,
    runDecls,
    runGhc,
    setContext,
    setSessionDynFlags,
 )
import GHC.Builtin.Types (consDataCon, nilDataCon, tupleDataCon)
import GHC.Core.ConLike (ConLike (RealDataCon))
import GHC.Core.DataCon (dataConWrapId)
import GHC.Core.Multiplicity (scaledThing)
import GHC.Core.Type (Type, mkScaledFunTys)
import GHC.Driver.Env (hsc_logger)
import qualified GHC.Driver.Monad as Driver
import GHC.Tc.Module (runTcInteractive)
import GHC.Tc.Types.Origin (SkolemInfoAnon (RuntimeUnkSkol), mkSkolemInfo)
import GHC.Tc.Utils.Instantiate (topSkolemise)
import GHC.Tc.Utils.Monad (TcM, getTcLevel)
import GHC.Tc.Utils.TcType (pushTcLevel, tcSplitFunTys)
import GHC.Types.Basic (Boxity (Boxed))
import GHC.Types.Id (Id)
import GHC.Types.Name (Name, getName, isSymOcc, nameOccName, occNameString)
import GHC.Types.SourceError (handleSourceError)
import GHC.Types.SrcLoc (noLoc)
import GHC.Types.Var (binderVar)

-- | A running GHC session.
newtype Session = Session Driver.Session

{- | Start a GHC session with the import declarations in scope and run the
action with it. The library directory comes from the variable @GHC_LIBDIR@,
or else from @ghc --print-libdir@.
-}
withSession :: [String] -> (Session -> IO a) -> IO a
withSession = withSessionPackages []

-- | 'withSession' with the given packages exposed too, besides @containers@.
withSessionPackages :: [String] -> [String] -> (Session -> IO a) -> IO a
withSessionPackages packages imports action = do
    libdir <- maybe (takeWhile (/= '\n') <$> readProcess "ghc" ["--print-libdir"] "") pure =<< lookupEnv "GHC_LIBDIR"
    runGhc (Just libdir) $ do
        flags <- getSessionDynFlags
        logger <- hsc_logger <$> getSession
        (parsed, _, _) <-
            parseDynamicFlags
                logger
                flags
                -- QuantifiedConstraints, so that a signature can have a
                -- quantified context.
                (map noLoc ("-w" : "-XQuantifiedConstraints" : concatMap (\package -> ["-package", package]) ("containers" : packages)))
        _ <- setSessionDynFlags parsed
        declarations <- traverse parseImportDecl imports
        setContext (map IIDecl declarations)
        Driver.reifyGhc (action . Session)

-- | Run a session action from 'IO'.
inSession :: Session -> Ghc a -> IO a
inSession (Session session) action = Driver.reflectGhc action session

-- | A module of a library: its name, and the qualifier of its names when the context imports it qualified.
data Import = Import
    { importModule :: String
    , importQualifier :: Maybe String
    }
    deriving (Eq, Show)

{- | The values that the modules export, each once, as candidates with the
text that the context gives them, and the list and pair constructors, which
are syntax and not exports. @($)@ and @id@ are arguments only, as in Hectare.
-}
candidatesOf :: Session -> [Import] -> IO [Candidate]
candidatesOf session imports = inSession session $ do
    exported <- fmap concat . forM imports $ \(Import moduleName qualifier) -> do
        found <- findModule (mkModuleName moduleName) Nothing
        info <- getModuleInfo found
        let names = maybe [] modInfoExports info
        things <- traverse lookupName names
        pure
            [ (name, textOf qualifier name, identifier)
            | (name, Just thing) <- zip names things
            , Just identifier <- [identifierOf thing]
            ]
    let unique = go Set.empty exported
        go _ [] = []
        go seen ((name, text, identifier) : rest)
            | name `Set.member` seen = go seen rest
            | otherwise = (text, identifier) : go (Set.insert name seen) rest
        builtIns = [("[]", dataConWrapId nilDataCon), ("(:)", dataConWrapId consDataCon), ("(,)", dataConWrapId (tupleDataCon Boxed 2))]
    pure
        [ (candidateFromId text identifier){candidateHeads = text `notElem` ["($)", "id"]}
        | (text, identifier) <- unique <> builtIns
        ]
  where
    identifierOf :: TyThing -> Maybe Id
    identifierOf thing = case thing of
        AnId identifier -> Just identifier
        AConLike (RealDataCon constructor) -> Just (dataConWrapId constructor)
        _ -> Nothing
    textOf :: Maybe String -> Name -> Text
    textOf qualifier name =
        let occurrence = nameOccName (getName name)
            text = maybe "" (<> ".") qualifier <> occNameString occurrence
         in Text.pack (if isSymOcc occurrence then "(" <> text <> ")" else text)

-- | The type of an expression as GHC infers it, or 'Nothing' when it does not typecheck.
typeOfExpression :: Session -> String -> IO (Maybe Type)
typeOfExpression session expression =
    inSession session $ handleSourceError (const (pure Nothing)) (Just <$> exprType TM_Inst expression)

-- | Whether an expression typechecks in the context.
accepts :: Session -> String -> IO Bool
accepts session expression = isJust <$> typeOfExpression session expression

{- | Run a typechecker action in the interactive context, as GHCi does for
@:type@. 'Nothing' when the action fails.
-}
inTypechecker :: Session -> TcM a -> IO (Maybe a)
inTypechecker session action = inSession session $ do
    environment <- getSession
    snd <$> liftIO (runTcInteractive environment action)

{- | Stream the fits of a signature: 'streamFits' on the hole of
'inSignatureHole', with the signature's arguments as required candidates
of the given names.
-}
fitsForSignature :: Session -> Options -> [Candidate] -> Type -> [Text] -> (Fit -> TcM Bool) -> IO (Maybe Statistics)
fitsForSignature session options candidates signature arguments accept =
    inSignatureHole session candidates signature arguments $ \hole candidates' goal ->
        streamFits options hole candidates' goal accept

{- | Run a search on the hole of a signature: skolemise the signature (its
type variables become skolems and its class context the givens), make the
hole of the skolems and givens ('holeFor'), and give the search the hole,
the candidates with the signature's arguments as required candidates of
the given names, and the goal. 'Nothing' when the typechecker action fails.
-}
inSignatureHole ::
    Session -> [Candidate] -> Type -> [Text] -> (TypedHole -> [Candidate] -> Type -> TcM a) -> IO (Maybe a)
inSignatureHole session candidates signature arguments search =
    inTypechecker session $ do
        information <- mkSkolemInfo RuntimeUnkSkol
        (_, skolems, givens, rho) <- topSkolemise information signature
        -- The skolems are one level deeper than the current level.
        level <- pushTcLevel <$> getTcLevel
        hole <- holeFor level (map (binderVar . snd) skolems) givens
        let (parameters, result) = tcSplitFunTys rho
            arity = length arguments
            required = [Candidate name (scaledThing parameter) True True | (name, parameter) <- zip arguments parameters]
            goal = mkScaledFunTys (drop arity parameters) result
        search hole (candidates <> required) goal

-- | Add declarations to the interactive context, as GHCi does for a declaration at its prompt.
declare :: Session -> String -> IO ()
declare session declarations = inSession session (void (runDecls declarations))
