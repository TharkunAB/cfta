{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

{- | A signature from a GHC session: each function by its expression, with
distinct unconstrained type variables at A, B, C, D, and Acc. Each function
uses these carriers in the order of its type binders. GHC gives the type of
a function, and 'erase' of cfta-ghc makes it a type of the automaton. The
session compiles the function once with Int in place of each carrier.
Variables that occur in constraints stay concrete. Container class variables
use lists, and other constrained variables use Int. The session compiles the
generator and the equality of each required type, when QuickCheck and Eq
supply the required instances in the session. This includes function
generators whose domains have CoArbitrary instances.

The session is a session of cfta-ghc. It has the unit of QuickCheck of the
program ('quickCheckUnit') and the package database of the store of cabal
that has the unit ('storeDatabase'), so that the generators of the session
give the values of the program. The values of the session are untyped (see
'Value'), so SPECFTACULAR_CHECKED=1 does not test their applications.

The search runs inside the session, so that the compiled code stays loaded.

Phase 1 merges the carriers in the shared search engine. Phases 2 to 4 keep
the distinct variables of the signature. The session reserves the names A,
B, C, D, and Acc for its carriers. A function with more than five
unconstrained type variables is not supported.
-}
module Specftacular.GHC (
    withGhcSignature,
) where

import Control.Monad (filterM, when)
import qualified Data.Map as Map
import Data.Maybe (catMaybes, fromMaybe, listToMaybe, maybeToList)
import Data.Proxy (Proxy (..))
import Data.Text (Text)
import qualified Data.Text as T
import Data.Typeable (tyConPackage, typeRep, typeRepTyCon)
import GHC.Builtin.Types (intTy, listTyCon)
import GHC.Core.Predicate (getClassPredTys_maybe)
import GHC.Core.TyCon (TyCon)
import GHC.Core.Type (getTyVar_maybe, mkTyConTy, substTyWith, tyConsOfType)
import qualified GHC.Core.Type as GHC
import GHC.Exts (Any)
import GHC.Tc.Utils.TcType (tcSplitNestedSigmaTys)
import GHC.Types.Name (getName, getOccString, nameModule_maybe)
import GHC.Types.Unique.Set (nonDetEltsUniqSet)
import GHC.Types.Var.Set (elemVarSet)
import GHC.Unit.Module (moduleName, moduleNameString)
import GHC.Utils.Outputable (showPprUnsafe)
import System.Directory (
    XdgDirectory (XdgState),
    doesDirectoryExist,
    doesFileExist,
    getHomeDirectory,
    getXdgDirectory,
    listDirectory,
 )
import System.Environment (lookupEnv)
import System.FilePath ((<.>), (</>))
import System.IO (hPutStrLn, stderr)
import qualified Test.QuickCheck as QC
import Unsafe.Coerce (unsafeCoerce)

import Data.CFTA.GHC.Erase (erase)
import Data.CFTA.GHC.Session (
    SessionOptions (..),
    compileExpression,
    declare,
    defaultSessionOptions,
    typeOfExpression,
    withSessionOptions,
 )
import qualified Data.CFTA.Gen.Synthesis as Hectare

import Specftacular.Types

{- | Start a session with the imports and the declarations, build the
signature of the functions and the extra functions, each given by its name
and its expression, and run the action with the signature and the instances
of its types.
-}
withGhcSignature ::
    [String] ->
    [String] ->
    [(Text, String)] ->
    [(Text, String)] ->
    (Sig -> (TypeSkeleton -> Maybe Instance) -> IO a) ->
    IO a
withGhcSignature imports declarations functions extras action = do
    database <- storeDatabase quickCheckUnit
    let options =
            defaultSessionOptions
                { sessionPackageIds = [quickCheckUnit]
                , sessionPackageDbs = maybeToList database
                , sessionFlags = ["-XGeneralizedNewtypeDeriving", "-XDerivingStrategies"]
                , sessionCompile = True
                }
        qualifiedImports =
            [ "import qualified Test.QuickCheck as QC"
            , "import qualified Test.QuickCheck.Gen as QCG"
            , "import qualified Test.QuickCheck.Random as QCR"
            ]
    withSessionOptions options (imports <> qualifiedImports) $ \session -> do
        let typeOf expression = fromMaybe (error ("Specftacular.GHC: no type for " <> expression)) <$> typeOfExpression session expression
            -- A compiled expression, or Nothing when it does not typecheck.
            compiled = compileExpression session
        let carrierNames = ["A", "B", "C", "D", "Acc"]
        mapM_
            ( \name ->
                declare
                    session
                    ("newtype " <> name <> " = " <> name <> " Int deriving newtype (Eq, Ord, Show, QC.Arbitrary, QC.CoArbitrary)")
            )
            carrierNames
        mapM_ (declare session) declarations
        carrierTypes <- traverse (\name -> typeOf ("undefined :: " <> name)) carrierNames
        let function make (name, expression) = do
                typ <- typeOf expression
                let (bound, theta, body) = tcSplitNestedSigmaTys typ
                    constraints =
                        [ (getOccString cls, args)
                        | p <- theta
                        , Just (cls, args) <- [getClassPredTys_maybe p]
                        ]
                    constrained v = any (elemVarSet v . GHC.tyCoVarsOfType) theta
                    container v =
                        or
                            [ cls `elem` ["Foldable", "Traversable", "Functor", "Applicative", "Monad"]
                            | (cls, args) <- constraints
                            , Just v `elem` map getTyVar_maybe args
                            ]
                    abstract = filter (not . constrained) bound
                    bindings = zip abstract carrierTypes
                    -- A variable of a class of containers or monads is the
                    -- list, any other constrained variable is Int, and each
                    -- unconstrained variable has a distinct abstract carrier.
                    at choose v
                        | container v = mkTyConTy listTyCon
                        | constrained v = intTy
                        | otherwise = choose v
                    instantiated choose = substTyWith bound (map (at choose) bound) body
                    logicalCarrier v = fromMaybe (error "Specftacular.GHC: no carrier for a type variable") (lookup v bindings)
                    source = "(" <> expression <> ") :: " <> showPprUnsafe (instantiated (const intTy))
                when (length abstract > length carrierTypes) $
                    error ("Specftacular.GHC: more than five unconstrained type variables in " <> expression)
                value <- fromMaybe (error ("Specftacular.GHC: cannot compile " <> source)) <$> compiled source
                case skeletonOf (instantiated logicalCarrier) of
                    Just skeleton -> pure (name, make (Untyped (unsafeCoerce value)) skeleton)
                    Nothing -> error ("Specftacular.GHC: no type for " <> expression)
            -- The generator and the equality of a type, if the session has
            -- them. GHC resolves the instances of the required types,
            -- including function arguments and session declarations.
            -- The full types of signature functions do not need variables.
            instanceOf t = do
                let source = sourceType t
                gen <- compiled ("\\seed size -> QCG.unGen (QC.arbitrary :: QC.Gen (" <> source <> ")) (QCR.mkQCGen seed) size")
                case gen of
                    Nothing -> do
                        hPutStrLn stderr ("Specftacular.GHC: no generator for " <> source)
                        pure Nothing
                    Just g -> do
                        eq <- compiled ("(==) :: (" <> source <> ") -> (" <> source <> ") -> Bool")
                        pure $
                            Just
                                ( t
                                , Instance
                                    { inst_text = typeText t
                                    , inst_prefix = prefixOf t
                                    , inst_gen = Generator (\seed size -> Untyped ((unsafeCoerce g :: Int -> Int -> Any) seed size))
                                    , inst_eq = Untyped . unsafeCoerce <$> eq
                                    }
                                )
        sigFunctions <- traverse (function SigFunc) functions
        extraFunctions <- traverse (function GenFunc) extras
        let sig = Map.fromList (sigFunctions <> extraFunctions)
            types = Map.keys (Map.fromList [(t, ()) | t <- instanceTypes monomorphiseType sig <> instanceTypes id sig])
        table <- Map.fromList . catMaybes <$> traverse instanceOf types
        -- Each physical key has the same generator and equality source.
        -- Ascending logical keys give a deterministic choice on collisions.
        let physicalTable = Map.fromList [(physicalType t, inst) | (t, inst) <- Map.toAscList table]
            resolve t = case Map.lookup t table of
                Just inst -> Just inst
                Nothing ->
                    (\inst -> inst{inst_text = typeText t, inst_prefix = prefixOf t})
                        <$> Map.lookup (physicalType t) physicalTable
        action sig resolve

{- | The unit of QuickCheck of the program: the package of the type of its
generators.
-}
quickCheckUnit :: String
quickCheckUnit = tyConPackage (typeRepTyCon (typeRep (Proxy :: Proxy (QC.Gen ()))))

{- | The package database of the store of cabal that has a unit. cabal keeps
its store in $CABAL_DIR/store, in ~/.cabal/store, or in the XDG state
directory, with one package database for each compiler. Nothing when no
store has the unit, as when the unit is in the global database.
-}
storeDatabase :: String -> IO (Maybe FilePath)
storeDatabase unit = do
    cabalDir <- lookupEnv "CABAL_DIR"
    home <- getHomeDirectory
    state <- getXdgDirectory XdgState "cabal"
    let stores = [dir </> "store" | Just dir <- [cabalDir]] <> [home </> ".cabal" </> "store", state </> "store"]
    databases <- concat <$> traverse compilers stores
    listToMaybe <$> filterM (\database -> doesFileExist (database </> unit <.> "conf")) databases
  where
    compilers store = do
        exists <- doesDirectoryExist store
        if exists then map (\compiler -> store </> compiler </> "package.db") <$> listDirectory store else pure []

{- | The type of the automaton of a GHC type: the type of 'erase', with the
names of the type constructors as 'typeRepToTypeSkeleton' gives them. The
carriers of the session are the carriers of "Specftacular.Types".
-}
skeletonOf :: GHC.Type -> Maybe TypeSkeleton
skeletonOf typ = convert <$> erase (const Nothing) typ
  where
    names = Map.fromList [(getOccString tc, qualified tc) | tc <- nonDetEltsUniqSet (tyConsOfType typ)]
    qualified :: TyCon -> Text
    qualified tc = case (getOccString tc, nameModule_maybe (getName tc)) of
        (occ, Just m)
            | occ `elem` ["A", "B", "C", "D", "Acc"]
            , "Ghci" `T.isPrefixOf` T.pack (moduleNameString (moduleName m)) ->
                "Specftacular.Types." <> T.pack occ
        (occ, Just m) -> T.pack (moduleNameString (moduleName m) <> "." <> occ)
        (occ, Nothing) -> T.pack occ
    convert (Hectare.TVar v) = TVar v
    convert (Hectare.TFun a b) = TFun (convert a) (convert b)
    convert (Hectare.TCons "List" [a]) = TCons "[]" [convert a]
    convert (Hectare.TCons "Unit" []) = TCons "()" []
    convert (Hectare.TCons "Pair" [a, b]) = TCons "(,)" [convert a, convert b]
    convert (Hectare.TCons name args) = TCons (Map.findWithDefault name (T.unpack name) names) (map convert args)

{- | The physical type used by the session. This uses the carrier test of
'sourceType' and keeps all other type constructors. Equal physical types
therefore use the same compiled generator and equality expressions.
-}
physicalType :: TypeSkeleton -> TypeSkeleton
physicalType t | t `elem` map fst carriers = typeSkeletonOf (Proxy :: Proxy Int)
physicalType (TCons name args) = TCons name (map physicalType args)
physicalType (TFun a b) = TFun (physicalType a) (physicalType b)
physicalType t = t

{- | A type as Haskell source, with each type constructor by its name
without its module, and Int for each abstract carrier.
-}
sourceType :: TypeSkeleton -> String
sourceType t | t `elem` map fst carriers = "Int"
sourceType (TCons "[]" [a]) = "[" <> sourceType a <> "]"
sourceType (TCons "(,)" [a, b]) = "(" <> sourceType a <> ", " <> sourceType b <> ")"
sourceType (TCons "()" []) = "()"
sourceType (TFun a b) = "(" <> sourceType a <> " -> " <> sourceType b <> ")"
sourceType (TCons name []) = unqualified name
sourceType (TCons name args) = "(" <> unwords (unqualified name : map sourceType args) <> ")"
sourceType (TVar v) = T.unpack v

-- | A type as 'show' of a 'TypeRep' gives it: @[A]@, @A -> B@, @(A,B)@.
typeText :: TypeSkeleton -> Text
typeText = T.pack . go False
  where
    go _ (TCons "[]" [a]) = "[" <> go False a <> "]"
    go _ (TCons "(,)" [a, b]) = "(" <> go False a <> "," <> go False b <> ")"
    go _ (TCons "()" []) = "()"
    go p (TFun a b) = parens p (go True a <> " -> " <> go False b)
    go _ (TCons name []) = unqualified name
    go p (TCons name args) = parens p (unwords (unqualified name : map (go True) args))
    go _ (TVar v) = T.unpack v
    parens True s = "(" <> s <> ")"
    parens False s = s

{- | The prefix of the names of the variables of a type: xs for a list, f
for a function, and x for any other type.
-}
prefixOf :: TypeSkeleton -> Text
prefixOf (TCons "[]" _) = "xs"
prefixOf (TFun _ _) = "f"
prefixOf _ = "x"

-- | The name of a type constructor without its module.
unqualified :: Text -> String
unqualified name = T.unpack (last (T.splitOn "." name))
