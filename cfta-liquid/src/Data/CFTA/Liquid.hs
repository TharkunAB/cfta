{-# LANGUAGE AllowAmbiguousTypes #-}

{- | Derive a refinement generator from the Liquid Haskell specification of a
datatype.

The specification is the text of the @{\-\@ \@-\}@ comments of a module, as
Liquid Haskell reads it. The parser of @liquidhaskell-boot@ reads the text,
without a GHC session and without the checker. The translation reads three
kinds of specification:

* the @data@ (or @newtype@) specification of the datatype: the refinement of
  each field is a conjunct of the contract of its constructor;
* one @measure@ of the datatype: its equations are the measures of the
  constructors;
* @type@ aliases with a refinement, such as @type Pos = {v:Int | v > 0}@,
  which a field type can name.

For example, the sorted lists of SortedLists.hs:

@
{\-\@ measure hd :: IncList -> Integer
        hd Emp = 1000001
        hd (Cons x xs) = x
  \@-\}
{\-\@ data IncList = Emp
                 | Cons { x :: {v:Integer | 0 <= v && v <= 1000000}, xs :: {v:IncList | x <= hd v} } \@-\}
@

The equations of a measure are indented more than the word @measure@, as
the layout rule of the Liquid Haskell parser requires. With the equations at
the column of @measure@, the parser reads an equation as a new
specification, and the error is "unexpected Em, expecting :: or ','".

Haddock text that shows a specification must not contain the two characters
that open a Haskell block comment (a left brace and a hyphen) or the two that
close it (a hyphen and a right brace): the first pair opens a nested comment,
and the second pair ends the comment. Escape the hyphen and the at sign with a
backslash, as the example above does in the source of this module.

The refinement of a field names the field as its value @v@, the earlier
fields by their names, and the measure of a field of the datatype as @hd xs@.
The result is the annotation list of 'deriveLTAWith', so the generator is the
generator of the same annotations in the expression language.

The translation is exact or it fails. It rejects, with 'Untranslatable', each
part that it cannot translate exactly: a second measure of the datatype (a
node of a liquid tree automaton has one integer), a measure equation that is
missing or that is not a term, abstract refinements, a name that is not a
field, an application of another function, division, and a product of two
terms that are not constants. Other kinds of specification, such as function
signatures, are not about the datatype, and the translation ignores them.
-}
module Data.CFTA.Liquid (
    -- * Specifications
    Specifications,
    specifications,
    specificationsOf,
    specificationComments,
    parseSpecifications,

    -- * Translation
    LiquidError (..),
    liquidAnnotations,
    deriveLTAFromLiquid,
    renderParseError,
) where

import Control.Monad (forM, unless, when)
import Data.Bifunctor (first)
import Data.List (find, intercalate)
import qualified Data.Map.Strict as Map
import Data.Proxy (Proxy (Proxy))
import Data.Typeable (TypeRep, tyConName, typeRepTyCon)
import Text.Megaparsec.Pos (SourcePos (SourcePos), mkPos, unPos)
import qualified Text.PrettyPrint.HughesPJ as PJ

import qualified Language.Fixpoint.Types as F
import Language.Haskell.Liquid.Parse (BPspec (..), parseSpecComments)
import Language.Haskell.Liquid.Types.DataDecl (DataCtorP (..), DataDeclP (..), DataName (..))
import Language.Haskell.Liquid.Types.Errors (ppError)
import Language.Haskell.Liquid.Types.Names (LHName, getLHNameSymbol)
import Language.Haskell.Liquid.Types.RType (BTyCon (..), BareTypeParsed, PredicateBV (..), RTypeBV (..), UReftBV (..))
import Language.Haskell.Liquid.Types.Types (BodyV (..), DefV (..), Error, MeasureV (..), RTAlias (..))

import Data.CFTA.Gen.Refinement (LTAGen)
import Data.CFTA.Gen.Refinement.Derive (Annotation, Atoms, DeriveLTAError, deriveLTAWith, fieldsContract, fieldsMeasure)
import Data.CFTA.Generic (Constructor (..), Description (..), HasFTA (..))
import Data.CFTA.Index (Depth)
import Data.CFTA.Refinement.Expression (
    Expr,
    Formula,
    false,
    lnot,
    true,
    (.&&),
    (./=),
    (.<),
    (.<=),
    (.==),
    (.>),
    (.>=),
    (.||),
 )

-- | The text of the @{\-\@ \@-\}@ comments of a module, each with its position.
newtype Specifications = Specifications [(SourcePos, String)]

{- | Specifications from the file, the line, the column, and the text of each
comment. The Template Haskell splice of "Data.CFTA.Liquid.TH" gives them.
-}
specifications :: [(FilePath, Int, Int, String)] -> Specifications
specifications comments =
    Specifications [(SourcePos file (mkPos line) (mkPos column), text) | (file, line, column, text) <- comments]

{- | The specifications in the source text of a module. The text of a comment
starts after its @{\-\@@, as Liquid Haskell gives it to its parser.
-}
specificationsOf :: FilePath -> String -> Specifications
specificationsOf file source =
    Specifications [(SourcePos file (mkPos line) (mkPos column), text) | (line, column, text) <- scan 1 1 source]
  where
    scan :: Int -> Int -> String -> [(Int, Int, String)]
    scan line column text = case text of
        '{' : '-' : '@' : rest ->
            let (body, after, line', column') = close line (column + 3) rest []
             in (line, column + 3, body) : scan line' column' after
        '\n' : rest -> scan (line + 1) 1 rest
        _ : rest -> scan line (column + 1) rest
        [] -> []
    close line column text accumulated = case text of
        '@' : '-' : '}' : rest -> (reverse accumulated, rest, line, column + 3)
        '\n' : rest -> close (line + 1) 1 rest ('\n' : accumulated)
        character : rest -> close line (column + 1) rest (character : accumulated)
        [] -> (reverse accumulated, [], line, column)

-- | The file, the line, the column, and the text of each comment, as 'specifications' takes them.
specificationComments :: Specifications -> [(FilePath, Int, Int, String)]
specificationComments (Specifications comments) =
    [(file, unPos line, unPos column, text) | (SourcePos file line column, text) <- comments]

-- | Parse the specifications with the parser of Liquid Haskell.
parseSpecifications :: Specifications -> Either LiquidError [BPspec]
parseSpecifications (Specifications comments) = case parseSpecComments comments of
    Right parsed -> Right parsed
    Left errors -> Left $ ParseErrors $ case located of
        [] -> map renderParseError errors
        _ -> located
  where
    -- The comments that fail alone, each error with the position of its comment.
    located =
        [ file <> ":" <> show (unPos line) <> ":" <> show (unPos column) <> ": " <> renderParseError err
        | comment@(SourcePos file line column, _) <- comments
        , Left errors <- [parseSpecComments [comment]]
        , err <- errors
        ]

-- | Failure while translating a specification.
data LiquidError
    = -- | The parser of Liquid Haskell rejects the specifications. Each text is one error.
      ParseErrors ![String]
    | -- | The specifications have no @data@ or @newtype@ specification of the named type.
      NoDataSpecification !String
    | {- | A part of a specification that the translation cannot translate
      exactly. The fields are the place, such as a field of a constructor, and
      the reason.
      -}
      Untranslatable !String !String
    | -- | The derivation rejects the translated annotations.
      DerivationFailed !DeriveLTAError
    deriving (Eq, Show)

-- | The text of one error of the Liquid Haskell parser.
renderParseError :: Error -> String
renderParseError err = PJ.render $ ppError F.Full PJ.empty (PJ.empty <$ err)

{- | Derive the refinement generator of a datatype from its Liquid Haskell
specification. This is 'deriveLTAWith' with the annotations of
'liquidAnnotations'.
-}
deriveLTAFromLiquid :: forall a. (HasFTA a) => Depth -> Atoms -> Specifications -> Either LiquidError (LTAGen a)
deriveLTAFromLiquid bound atoms specs = do
    annotations <- liquidAnnotations @a specs
    first DerivationFailed $ deriveLTAWith @a bound atoms annotations

{- | The annotations of the constructors of a datatype, from the @data@
specification, the measure, and the aliases of the datatype.
-}
liquidAnnotations :: forall a. (HasFTA a) => Specifications -> Either LiquidError [(String, Annotation)]
liquidAnnotations specs = do
    parsed <- parseSpecifications specs
    (datatype, alternatives) <- case describeType (Proxy @a) of
        AlgebraicType datatype alternatives -> Right (datatype, alternatives)
        AtomicType datatype -> Left $ Untranslatable (show datatype) "an atomic type has no constructors"
    let typeName = tyConName $ typeRepTyCon datatype
        aliases = Map.fromList [(nameOf $ F.val $ rtName alias, alias) | Alias alias <- parsed]
        declarations =
            [declaration | DDecl declaration <- parsed, dataNameOf declaration == typeName]
                <> [declaration | NTDecl declaration <- parsed, dataNameOf declaration == typeName]
        measures = [measureSpec | Meas measureSpec <- parsed, measureTypeOf measureSpec == Just typeName]
    declaration <- case declarations of
        [declaration] -> Right declaration
        [] -> Left $ NoDataSpecification typeName
        _ -> Left $ Untranslatable typeName "there is more than one data specification"
    unless (null $ tycPVars declaration) $ Left $ Untranslatable typeName "abstract refinements are not translated"
    measureSpec <- case measures of
        [] -> Right Nothing
        [measureSpec] -> Right $ Just measureSpec
        _ ->
            Left
                $ Untranslatable typeName
                $ "the measures "
                    <> intercalate ", " [nameOf $ F.val $ msName measureSpec | measureSpec <- measures]
                    <> " are more than one: a node of a liquid tree automaton has one integer"
    let measureName = nameOf . F.val . msName <$> measureSpec
    ctors <-
        maybe (Left $ Untranslatable typeName "the data specification has no constructors") Right $ tycDCons declaration
    forM alternatives $ \(constructor, children) -> do
        let name = constructorName constructor
            recursive = [descriptionType child == datatype | child <- children]
            arity = length children
        declared <-
            maybe (Left $ Untranslatable typeName $ "the data specification has no constructor " <> name) Right $
                find ((== name) . nameOf . F.val . dcName) ctors
        let fields = dcFields declared
        unless (length fields == arity)
            $ Left
            $ Untranslatable name
            $ "the specification has " <> show (length fields) <> " fields, and the datatype has " <> show arity
        let fieldNames = [F.symbolString $ getLHNameSymbol fieldName | (fieldName, _) <- fields]
        conjuncts <- fmap concat $ forM (zip3 [0 ..] fields recursive) $ \(position, (_, fieldType), isRecursive) -> do
            let place = "field " <> fieldNames !! position <> " of " <> name
            refinements <- refinementsOf place aliases fieldType
            forM refinements $ \(binder, expression) -> do
                let scope =
                        Map.insert (F.symbolString binder) (position, isRecursive) $
                            Map.fromList [(field, (index, recursive !! index)) | (index, field) <- zip [0 ..] fieldNames]
                formulaOf place measureName scope expression
        let contractPart
                | null conjuncts = mempty
                | otherwise = fieldsContract arity $ \terms -> foldr1 (.&&) [conjunct terms | conjunct <- conjuncts]
        measurePart <- case measureSpec of
            Nothing -> Right mempty
            Just measureSpec' -> do
                let place = "the measure " <> concat measureName <> " of " <> name
                equation <-
                    maybe (Left $ Untranslatable place "the measure has no equation for this constructor") Right $
                        find ((== name) . nameOf . F.val . ctor) (msEqns measureSpec')
                let binders = [F.symbolString binder | (binder, _) <- binds equation]
                when (length binders /= arity)
                    $ Left
                    $ Untranslatable place
                    $ "the equation binds " <> show (length binders) <> " fields, and the constructor has " <> show arity
                case body equation of
                    E expression -> do
                        termOf' <-
                            termOf
                                place
                                measureName
                                (Map.fromList [(binder, (index, recursive !! index)) | (index, binder) <- zip [0 ..] binders])
                                expression
                        Right $ fieldsMeasure arity termOf'
                    _ -> Left $ Untranslatable place "the equation is a predicate, not a term"
        pure (name, contractPart <> measurePart)

-- | The name of a Liquid Haskell name, without its qualification.
nameOf :: LHName -> String
nameOf = F.symbolString . getLHNameSymbol

-- | The name of the type of a data specification.
dataNameOf :: DataDeclP v ty -> String
dataNameOf declaration = case tycName declaration of
    DnName name -> nameOf $ F.val name
    DnCon name -> nameOf $ F.val name

-- | The name of the type that a measure takes, as in @hd :: IncList -> Integer@.
measureTypeOf :: MeasureV v (F.Located (RTypeBV b v BTyCon tv r)) ctor -> Maybe String
measureTypeOf measureSpec = case F.val $ msSort measureSpec of
    RFun{rt_in = RApp{rt_tycon}} -> Just $ nameOf $ F.val $ btc_tc rt_tycon
    _ -> Nothing

-- | The type that a description describes.
descriptionType :: Description -> TypeRep
descriptionType (AtomicType typ) = typ
descriptionType (AlgebraicType typ _) = typ

{- | The refinements of a field type: its own, and those of the aliases that it
names, each with its binder.
-}
refinementsOf ::
    String ->
    Map.Map String (RTAlias F.Symbol BareTypeParsed) ->
    BareTypeParsed ->
    Either LiquidError [(F.Symbol, F.ExprV F.LocSymbol)]
refinementsOf place aliases = go (8 :: Int)
  where
    go depth fieldType = case fieldType of
        RApp{rt_tycon, rt_args, rt_reft}
            | Just alias <- Map.lookup (nameOf $ F.val $ btc_tc rt_tycon) aliases -> do
                when (depth <= 0) $ Left $ Untranslatable place "the aliases expand more than eight times"
                unless (null rt_args && null (rtTArgs alias) && null (rtVArgs alias))
                    $ Left
                    $ Untranslatable place "an alias with arguments is not translated"
                (<>) <$> go (depth - 1) (rtBody alias) <*> own rt_reft
            | otherwise -> own rt_reft
        RVar{rt_reft} -> own rt_reft
        _ -> Left $ Untranslatable place "only a type constructor or a type variable with a refinement is translated"
    own (MkUReft (F.Reft (binder, expression)) (Pr predicates))
        | not (null predicates) = Left $ Untranslatable place "abstract refinements are not translated"
        | F.PAnd [] <- expression = Right []
        | otherwise = Right [(binder, expression)]

-- | The fields in scope: each name with its position and whether its type is the datatype.
type Scope = Map.Map String (Int, Bool)

-- | Translate a refinement into a formula of the terms of the fields.
formulaOf :: String -> Maybe String -> Scope -> F.ExprV F.LocSymbol -> Either LiquidError ([Expr] -> Formula)
formulaOf place measureName scope = go
  where
    go expression = case expression of
        F.PAnd [] -> Right $ const true
        F.POr [] -> Right $ const false
        F.PAnd parts -> foldr1 (\left right terms -> left terms .&& right terms) <$> traverse go parts
        F.POr parts -> foldr1 (\left right terms -> left terms .|| right terms) <$> traverse go parts
        F.PNot inner -> (lnot .) <$> go inner
        F.PImp left right -> (\l r terms -> lnot (l terms) .|| r terms) <$> go left <*> go right
        F.PIff left right ->
            (\l r terms -> (l terms .&& r terms) .|| (lnot (l terms) .&& lnot (r terms))) <$> go left <*> go right
        F.PAtom relation left right -> do
            compare' <- relationOf relation
            (\l r terms -> compare' (l terms) (r terms))
                <$> termOf place measureName scope left
                <*> termOf place measureName scope right
        F.ECst inner _ -> go inner
        _ -> Left $ Untranslatable place $ "the formula " <> show expression <> " is not translated"
    relationOf relation = case relation of
        F.Eq -> Right (.==)
        F.Ueq -> Right (.==)
        F.Ne -> Right (./=)
        F.Une -> Right (./=)
        F.Lt -> Right (.<)
        F.Le -> Right (.<=)
        F.Gt -> Right (.>)
        F.Ge -> Right (.>=)

{- | Translate a term into a term of the terms of the fields. An atomic field
is its own term. A field of the datatype has a term only through the measure.
-}
termOf :: String -> Maybe String -> Scope -> F.ExprV F.LocSymbol -> Either LiquidError ([Expr] -> Expr)
termOf place measureName scope = go
  where
    go expression = case expression of
        F.ECon (F.I value) -> Right $ const $ fromInteger value
        F.EVar name -> case Map.lookup (F.symbolString $ F.val name) scope of
            Just (position, False) -> Right (!! position)
            Just (_, True) ->
                Left
                    $ Untranslatable place
                    $ F.symbolString (F.val name) <> " is a value of the datatype; read it through the measure"
            Nothing -> Left $ Untranslatable place $ F.symbolString (F.val name) <> " is not a field"
        F.EApp (F.EVar function) (F.EVar argument)
            | Just (F.symbolString $ F.val function) == measureName ->
                case Map.lookup (F.symbolString $ F.val argument) scope of
                    Just (position, True) -> Right (!! position)
                    Just (_, False) ->
                        Left
                            $ Untranslatable place
                            $ "the measure is applied to the atomic field " <> F.symbolString (F.val argument)
                    Nothing -> Left $ Untranslatable place $ F.symbolString (F.val argument) <> " is not a field"
        F.EApp{} -> Left $ Untranslatable place $ "the application " <> show expression <> " is not the measure of a field"
        F.ENeg inner -> (negate .) <$> go inner
        F.EBin F.Plus left right -> (\l r terms -> l terms + r terms) <$> go left <*> go right
        F.EBin F.Minus left right -> (\l r terms -> l terms - r terms) <$> go left <*> go right
        F.EBin F.Times left@(F.ECon _) right -> (\l r terms -> l terms * r terms) <$> go left <*> go right
        F.EBin F.Times left right@(F.ECon _) -> (\l r terms -> l terms * r terms) <$> go left <*> go right
        F.EBin F.Times _ _ -> Left $ Untranslatable place "a product of two terms that are not constants is not linear"
        F.EBin operator _ _ -> Left $ Untranslatable place $ "the operator " <> show operator <> " is not translated"
        F.ECst inner _ -> go inner
        _ -> Left $ Untranslatable place $ "the term " <> show expression <> " is not translated"
