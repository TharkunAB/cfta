{-# LANGUAGE OverloadedStrings #-}

{- | A corpus of programs from Haskell sources, in the alphabet of the
automata of mode (b), for a fit model ("Data.CFTA.GHC.Model").

'moduleTerms' parses a module with GHC's parser, with the language pragmas
of the module. Each maximal application becomes a term: a node for each
head, with its arguments as children. The symbol of a node is the name of
its head and its number of arguments, as @map/2@. A head is a candidate
when its name is the text of a candidate and its qualifier, if any, names a
module of the candidates. Every other variable or constructor is @var@. A
literal, a lambda, and every other expression is the leaf @other/0@, and the
corpus looks for applications inside it. @f $ x@ is @f x@, @(a, b)@ is @(,)@
with two arguments, and @[]@ is the empty list. The root of the body of a
right-hand side (of a function, a case alternative, or a lambda) has the
parent @top@; the root of another application has the parent @expr@.
-}
module Data.CFTA.GHC.Corpus (
    Parser,
    newParser,
    parserOf,
    moduleTerms,
) where

import Control.Exception (SomeException, evaluate, try)
import Data.Data (Data, cast, gmapQ)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text

import GHC (getSessionDynFlags)
import GHC.Data.FastString (mkFastString)
import GHC.Data.StringBuffer (hGetStringBuffer)
import GHC.Driver.Config.Parser (initParserOpts)
import GHC.Driver.DynFlags (DynFlags, targetPlatform, xopt)
import GHC.Driver.Session (parseDynamicFilePragma, supportedLanguagesAndExtensions)
import GHC.Hs
import GHC.LanguageExtensions (Extension (Cpp))
import GHC.Parser (parseModule)
import GHC.Parser.Header (getOptions)
import GHC.Parser.Lexer (ParseResult (..), initParserState, unP)
import GHC.Platform (platformArchOS)
import GHC.Types.Name (nameOccName)
import GHC.Types.Name.Occurrence (OccName, isSymOcc, occNameString)
import GHC.Types.Name.Reader (RdrName (..))
import GHC.Types.SrcLoc (GenLocated (L), mkRealSrcLoc, unLoc)
import GHC.Utils.Logger (Logger, getLogger)

import Data.CFTA.GHC.Session (Session, inSession)
import Data.CFTA.Term (Term (..))

-- | What the parser of a session needs: its flags, its logger, and its language extensions.
data Parser = Parser DynFlags Logger [String]

-- | The parser of a session.
newParser :: Session -> IO Parser
newParser session = uncurry parserOf <$> inSession session ((,) <$> getSessionDynFlags <*> getLogger)

-- | The parser of the flags and the logger of a compilation, as a plugin has them.
parserOf :: DynFlags -> Logger -> Parser
parserOf flags logger = Parser flags logger (supportedLanguagesAndExtensions (platformArchOS (targetPlatform flags)))

{- | The terms of a module file, each with the parent of its root, for the
candidates of the given names from the given modules. 'Nothing' when the
module does not parse, or uses CPP.
-}
moduleTerms :: Parser -> [Text] -> Set.Set Text -> FilePath -> IO (Maybe [(Text, Term Text)])
moduleTerms (Parser flags logger supported) modules names file = do
    outcome <- try $ do
        buffer <- hGetStringBuffer file
        let (_, pragmas) = getOptions (initParserOpts flags) supported buffer file
        (moduleFlags, _, _) <- parseDynamicFilePragma logger flags pragmas
        if xopt Cpp moduleFlags
            then pure Nothing
            else case unP parseModule (initParserState (initParserOpts moduleFlags) buffer (mkRealSrcLoc (mkFastString file) 1 1)) of
                POk _ parsed -> do
                    let found = parsedTerms (map Text.unpack modules) names (unLoc parsed)
                    _ <- evaluate (length (show found))
                    pure (Just found)
                PFailed _ -> pure Nothing
    pure $ case outcome :: Either SomeException (Maybe [(Text, Term Text)]) of
        Right found -> found
        Left _ -> Nothing

-- | The terms of the maximal applications of a parsed module.
parsedTerms :: [String] -> Set.Set Text -> HsModule GhcPs -> [(Text, Term Text)]
parsedTerms modules names parsed = collect (hsmodDecls parsed)
  where
    -- The modules of each qualifier.
    qualifiers =
        Map.fromListWith
            (<>)
            [ ( moduleNameString $ unLoc $ fromMaybe (ideclName declaration) (ideclAs declaration)
              , [moduleNameString $ unLoc $ ideclName declaration]
              )
            | declaration <- map unLoc (hsmodImports parsed)
            ]
    collect :: (Data a) => a -> [(Text, Term Text)]
    collect value = case cast value :: Maybe (GRHS GhcPs (LHsExpr GhcPs)) of
        Just (GRHS _ guards body) -> concatMap collect guards <> rooted "top" (unLoc body)
        Nothing -> case cast value :: Maybe (HsExpr GhcPs) of
            Just expression -> rooted "expr" expression
            Nothing -> concat (gmapQ collect value)
    rooted parent expression =
        let (term, opaque) = convert expression
         in (parent, term) : concatMap (concat . gmapQ collect) opaque
    -- A term and the expressions that it leaves opaque.
    convert :: HsExpr GhcPs -> (Term Text, [HsExpr GhcPs])
    convert expression = case expression of
        HsVar _ name -> (Node (nameOf (unLoc name) <> "/0") [], [])
        HsPar _ inner -> convert (unLoc inner)
        HsAppType _ inner _ -> convert (unLoc inner)
        HsApp _ function argument -> applied (unLoc function) [unLoc argument]
        OpApp _ left (L _ (HsVar _ operator)) right
            | occNameString (rdrOcc $ unLoc operator) == "$" -> applied (unLoc left) [unLoc right]
            | otherwise -> node (nameOf $ unLoc operator) [unLoc left, unLoc right]
        ExplicitTuple _ [Present _ left, Present _ right] _ -> node "(,)" [unLoc left, unLoc right]
        ExplicitList _ [] -> (Node "[]/0" [], [])
        _ -> (Node "other/0" [], [expression])
    -- A head with more arguments: the arguments of the head first.
    applied function arguments = case convert function of
        (Node symbol children, opaque) ->
            let (terms, inner) = unzip (map convert arguments)
                name = Text.dropWhileEnd (/= '/') symbol
                every = children <> terms
             in (Node (name <> Text.pack (show (length every))) every, opaque <> concat inner)
    node name arguments =
        let (terms, inner) = unzip (map convert arguments)
         in (Node (name <> "/" <> Text.pack (show (length terms))) terms, concat inner)
    nameOf :: RdrName -> Text
    nameOf name = case name of
        Qual qualifier occurrence
            | any (`elem` modules) (Map.findWithDefault [moduleNameString qualifier] (moduleNameString qualifier) qualifiers) ->
                candidate occurrence
            | otherwise -> "var"
        _ -> candidate (rdrOcc name)
    candidate :: OccName -> Text
    candidate occurrence =
        let text = Text.pack (if isSymOcc occurrence then "(" <> occNameString occurrence <> ")" else occNameString occurrence)
         in if Set.member text names then text else "var"
    rdrOcc :: RdrName -> OccName
    rdrOcc name = case name of
        Unqual occurrence -> occurrence
        Qual _ occurrence -> occurrence
        Orig _ occurrence -> occurrence
        Exact exact -> nameOccName exact
