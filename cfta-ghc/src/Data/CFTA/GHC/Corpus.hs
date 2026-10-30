{-# LANGUAGE OverloadedStrings #-}

{- | A corpus of programs from Haskell sources, in the alphabet of the
automata of mode (b), for a fit model ("Data.CFTA.GHC.Model").

'moduleTerms' parses a module with GHC's parser, with the language pragmas
of the module. Each expression of a right-hand side becomes a term: a node
for each part, with its parts as children. The symbol of a node is a name
and its number of children, as @map/2@:

* an application has its head's name and its arguments, also through @$@
  and an operator; @f $ x@ and @f $! x@ are @f x@;
* a head is a candidate when its name is the text of a candidate and its
  qualifier, if any, names a module of the candidates; a name that a
  pattern around it binds (a parameter of the function or of a lambda, or a
  variable of an alternative or a bind) is @arg@; every other variable or
  constructor is @var@;
* a section @(x +)@ is @(+)@ with one argument, @(+ x)@ is @flip (+) x@, and
  @-x@ is @negate x@;
* a tuple is @(,)@, @(,,)@, ...; @[]@ is the empty list, and @[a, b]@ is
  @list/2@; a literal is @lit/0@;
* @if@ is @if/3@; a lambda is @lambda/1@ with its body; @case@ has the
  scrutinee and the body of each alternative; @let@ is @let/1@ with its
  body; @do@ has the expression of each statement; a lambda or an
  alternative with guards, and a statement other than an expression, a
  bind, or the last one, make the whole expression @other/0@;
* every other expression is @other/0@.

The corpus also takes the terms of the parts that a term leaves out:
guards, local bindings, patterns, and the insides of @other/0@. The root of
the body of a right-hand side has the parent @top@; the root of another
expression has the parent @expr@.
-}
module Data.CFTA.GHC.Corpus (
    Parser,
    newParser,
    parserOf,
    moduleTerms,
    moduleNames,
    holeContext,
) where

import Control.Exception (SomeException, evaluate, try)
import Data.Data (Data, cast, gmapQ)
import Data.List.NonEmpty (NonEmpty ((:|)))
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, listToMaybe)
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
import GHC.Types.SrcLoc (GenLocated (L), SrcSpan (RealSrcSpan), mkRealSrcLoc, srcSpanStartCol, srcSpanStartLine, unLoc)
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
moduleTerms parser modules names file = do
    found <- parseFile parser file
    case found of
        Nothing -> pure Nothing
        Just parsed -> do
            let terms = [(root, fmap withoutHoles term) | (root, term) <- parsedTerms (map Text.unpack modules) names parsed]
                withoutHoles symbol = if "_@" `Text.isPrefixOf` symbol then "var/0" else symbol
            outcome <- try (evaluate (length (show terms)))
            pure $ case outcome :: Either SomeException Int of
                Right _ -> Just terms
                Left _ -> Nothing

{- | How often the expressions of a module file use each unqualified name of
a variable or a constructor. Empty when the module does not parse, or uses
CPP.
-}
moduleNames :: Parser -> FilePath -> IO (Map.Map Text Int)
moduleNames parser file = maybe Map.empty (Map.fromListWith (+) . map (\name -> (name, 1)) . go . hsmodDecls) <$> parseFile parser file
  where
    go :: (Data a) => a -> [Text]
    go value = here <> concat (gmapQ go value)
      where
        here = case cast value :: Maybe (HsExpr GhcPs) of
            Just (HsVar _ name) | Unqual occurrence <- unLoc name -> [occurrenceText occurrence]
            _ -> []
    occurrenceText occurrence = Text.pack (if isSymOcc occurrence then "(" <> occNameString occurrence <> ")" else occNameString occurrence)

{- | The context of the hole that starts at a line and a column of a module
file: the symbol of the node whose child the hole is, with the node's number
of children, and the hole's position among them. In @foldr f _ xs@ the hole
has the context @(foldr/3, 1)@, and in @if _ then a else b@ the context
@(if/3, 0)@. A hole that is the root of a right-hand side has @top@, and the
root of another expression @expr@, both with the position 0. 'Nothing' when
the module does not parse, or has no such hole.
-}
holeContext :: Parser -> [Text] -> Set.Set Text -> FilePath -> (Int, Int) -> IO (Maybe (Text, Int))
holeContext parser modules names file start = do
    found <- parseFile parser file
    pure $ case found of
        Nothing -> Nothing
        Just parsed ->
            listToMaybe
                [context | (root, term) <- parsedTerms (map Text.unpack modules) names parsed, context <- contexts root term]
  where
    marker = holeSymbol start <> "/0"
    contexts root term@(Node symbol _)
        | symbol == marker = [(root, 0)]
        | otherwise = inner term
    inner (Node symbol children) =
        [(symbol, position) | (position, Node child _) <- zip [0 ..] children, child == marker] <> concatMap inner children

-- | The symbol of a hole at a line and a column, without its number of children.
holeSymbol :: (Int, Int) -> Text
holeSymbol (line, column) = "_@" <> Text.pack (show line) <> ":" <> Text.pack (show column)

-- | The parsed module of a file. 'Nothing' when it does not parse, or uses CPP.
parseFile :: Parser -> FilePath -> IO (Maybe (HsModule GhcPs))
parseFile (Parser flags logger supported) file = do
    outcome <- try $ do
        buffer <- hGetStringBuffer file
        let (_, pragmas) = getOptions (initParserOpts flags) supported buffer file
        (moduleFlags, _, _) <- parseDynamicFilePragma logger flags pragmas
        pure $
            if xopt Cpp moduleFlags
                then Nothing
                else case unP parseModule (initParserState (initParserOpts moduleFlags) buffer (mkRealSrcLoc (mkFastString file) 1 1)) of
                    POk _ parsed -> Just (unLoc parsed)
                    PFailed _ -> Nothing
    pure $ case outcome :: Either SomeException (Maybe (HsModule GhcPs)) of
        Right found -> found
        Left _ -> Nothing

{- | The text of a name in a parsed module: a candidate's text, when the
qualifier (if any) names one of the modules, and @var@ otherwise.
-}
namer :: [String] -> Set.Set Text -> HsModule GhcPs -> RdrName -> Text
namer modules names parsed name = case name of
    Qual qualifier occurrence
        | any (`elem` modules) (Map.findWithDefault [moduleNameString qualifier] (moduleNameString qualifier) qualifiers) ->
            candidate occurrence
        | otherwise -> "var"
    _ -> candidate (rdrOcc name)
  where
    qualifiers =
        Map.fromListWith
            (<>)
            [ ( moduleNameString $ unLoc $ fromMaybe (ideclName declaration) (ideclAs declaration)
              , [moduleNameString $ unLoc $ ideclName declaration]
              )
            | declaration <- map unLoc (hsmodImports parsed)
            ]
    candidate occurrence =
        let text = Text.pack (if isSymOcc occurrence then "(" <> occNameString occurrence <> ")" else occNameString occurrence)
         in if Set.member text names then text else "var"

-- | The occurrence of a name.
rdrOcc :: RdrName -> OccName
rdrOcc name = case name of
    Unqual occurrence -> occurrence
    Qual _ occurrence -> occurrence
    Orig _ occurrence -> occurrence
    Exact exact -> nameOccName exact

{- | The terms of a parsed module, each with the parent of its root. A name
that a pattern binds (a parameter of the enclosing function or lambda, or a
variable of a pattern of an enclosing alternative or bind) is @arg@. A hole
@_@ of the module is a leaf whose symbol holds its line and column, as
@_\@12:7/0@ ('holeSymbol').
-}
parsedTerms :: [String] -> Set.Set Text -> HsModule GhcPs -> [(Text, Term Text)]
parsedTerms modules names parsed = collect Set.empty (hsmodDecls parsed)
  where
    nameOf = namer modules names parsed
    -- The name of a variable, with the names that the patterns around it bind.
    nameIn bound name = case name of
        Unqual occurrence | Text.pack (occNameString occurrence) `Set.member` bound -> "arg"
        _ -> nameOf name
    collect :: (Data a) => Set.Set Text -> a -> [(Text, Term Text)]
    collect bound value = case cast value :: Maybe (Match GhcPs (LHsExpr GhcPs)) of
        Just match -> concat (gmapQ (collect (bound <> patternNames (m_pats match))) match)
        Nothing -> case cast value :: Maybe (GRHS GhcPs (LHsExpr GhcPs)) of
            Just (GRHS _ guards body) -> concatMap (collect bound) guards <> rooted bound "top" body
            Nothing -> case cast value :: Maybe (LHsExpr GhcPs) of
                Just expression -> rooted bound "expr" expression
                Nothing -> concat (gmapQ (collect bound) value)
    rooted bound parent expression = let (term, inner) = convert bound expression in (parent, term) : inner
    -- The children of a value that is not part of a term.
    within :: (Data a) => Set.Set Text -> a -> [(Text, Term Text)]
    within bound = concat . gmapQ (collect bound)
    -- A term, and the terms of the parts that it leaves out.
    convert :: Set.Set Text -> LHsExpr GhcPs -> (Term Text, [(Text, Term Text)])
    convert bound located@(L location expression) = case expression of
        HsVar _ name -> (Node (nameIn bound (unLoc name) <> "/0") [], [])
        HsPar _ inner -> convert bound inner
        HsAppType _ inner _ -> convert bound inner
        HsApp _ function argument -> applied bound function [argument]
        OpApp _ left (L _ (HsVar _ operator)) right
            | occNameString (rdrOcc $ unLoc operator) `elem` ["$", "$!"] -> applied bound left [right]
            | otherwise -> node bound (nameIn bound $ unLoc operator) [left, right] []
        SectionL _ left (L _ (HsVar _ operator)) -> node bound (nameIn bound $ unLoc operator) [left] []
        SectionR _ (L _ (HsVar _ operator)) right ->
            let (term, inner) = convert bound right
             in (Node "flip/2" [Node (nameIn bound (unLoc operator) <> "/0") [], term], inner)
        NegApp _ inner _ -> node bound "negate" [inner] []
        ExplicitTuple _ arguments _
            | Just present <- traverse presentOf arguments
            , length present >= 2 ->
                node bound ("(" <> Text.replicate (length present - 1) "," <> ")") present []
        ExplicitList _ [] -> (Node "[]/0" [], [])
        ExplicitList _ elements -> node bound "list" elements []
        HsLit _ _ -> (Node "lit/0" [], [])
        HsOverLit _ _ -> (Node "lit/0" [], [])
        HsIf _ condition yes no -> node bound "if" [condition, yes, no] []
        HsLam _ LamSingle (MG _ (L _ [L _ (Match _ _ patterns (GRHSs _ (L _ (GRHS _ [] body) :| []) binds))])) ->
            let bound' = bound <> patternNames patterns
             in node bound' "lambda" [body] (within bound' patterns <> within bound' binds)
        HsCase _ scrutinee (MG _ (L _ alternatives))
            | Just bodies <- traverse (unguarded bound . unLoc) alternatives ->
                let bound' = bound <> foldMap (\(L _ alternative) -> patternNames (m_pats alternative)) alternatives
                 in node bound' "case" (scrutinee : map fst bodies) (concatMap snd bodies)
        HsLet _ binds body -> node bound "let" [body] (within bound binds)
        HsDo _ _ (L _ statements)
            | Just parts <- traverse (statement bound . unLoc) statements ->
                let bound' = bound <> foldMap (\(L _ part) -> boundBy part) statements
                 in node bound' "do" (map fst parts) (concatMap snd parts)
        HsHole _
            | RealSrcSpan span' _ <- locA location ->
                (Node (holeSymbol (srcSpanStartLine span', srcSpanStartCol span') <> "/0") [], [])
        _ -> (Node "other/0" [], within bound located)
    presentOf argument = case argument of
        Present _ inner -> Just inner
        _ -> Nothing
    -- The body of an alternative without guards, and the terms of its patterns and local bindings.
    unguarded :: Set.Set Text -> Match GhcPs (LHsExpr GhcPs) -> Maybe (LHsExpr GhcPs, [(Text, Term Text)])
    unguarded bound (Match _ _ patterns (GRHSs _ (L _ (GRHS _ [] body) :| []) binds)) =
        let bound' = bound <> patternNames patterns
         in Just (body, within bound' patterns <> within bound' binds)
    unguarded _ _ = Nothing
    -- The expression of a statement, and the terms of its other parts.
    statement :: Set.Set Text -> StmtLR GhcPs GhcPs (LHsExpr GhcPs) -> Maybe (LHsExpr GhcPs, [(Text, Term Text)])
    statement bound part = case part of
        BodyStmt _ body _ _ -> Just (body, [])
        LastStmt _ body _ _ -> Just (body, [])
        BindStmt _ pattern body -> Just (body, within bound pattern)
        _ -> Nothing
    -- The names that a statement's pattern binds.
    boundBy :: StmtLR GhcPs GhcPs (LHsExpr GhcPs) -> Set.Set Text
    boundBy part = case part of
        BindStmt _ pattern _ -> patternNames pattern
        _ -> Set.empty
    -- A head with more arguments: the arguments of the head first.
    applied bound function arguments = case convert bound function of
        (Node symbol children, inner) ->
            let (terms, inners) = unzip (map (convert bound) arguments)
                name = Text.dropWhileEnd (/= '/') symbol
                every = children <> terms
             in (Node (name <> Text.pack (show (length every))) every, inner <> concat inners)
    node bound name arguments others =
        let (terms, inners) = unzip (map (convert bound) arguments)
         in (Node (name <> "/" <> Text.pack (show (length terms))) terms, concat inners <> others)

-- | The names that the variable patterns and the as-patterns of a value bind.
patternNames :: (Data a) => a -> Set.Set Text
patternNames value = here <> mconcat (gmapQ patternNames value)
  where
    here = case cast value :: Maybe (Pat GhcPs) of
        Just (VarPat _ name) -> Set.singleton (Text.pack (occNameString (rdrOcc (unLoc name))))
        Just (AsPat _ name _) -> Set.singleton (Text.pack (occNameString (rdrOcc (unLoc name))))
        _ -> Set.empty
