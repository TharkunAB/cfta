{-# LANGUAGE AllowAmbiguousTypes #-}

{- | Derive a refinement generator from the Liquid Haskell specification of a
datatype.

The specification is the text of the @{\-\@ \@-\}@ comments of a module, as
Liquid Haskell reads it. The parser of @liquidhaskell-boot@ reads the text,
without a GHC session and without the checker. The specification is the one
that Liquid Haskell verifies, with nothing that is special to cfta. The
tutorial's ordered lists:

@
data IncList a = Emp | (:<) { hd :: a, tl :: IncList a }

{\-\@ data IncList a = Emp
                   | (:<) { hd :: a, tl :: IncList {v:a | hd <= v} } \@-\}

{\-\@ type SortedBounded = IncList {v:Integer | 0 <= v && v <= 1000000} \@-\}
@

The generator enumerates a target: an alias without parameters, such as
@SortedBounded@, or the name of a datatype. The target is an instance of a
datatype at concrete element types:

@
sortedLists = deriveLTAFromLiquid \@(IncList Integer) 8 (atom \@Integer every) $(liquidSpecifications) "SortedBounded"
@

The translation reads these kinds of specification:

* the @data@ (or @newtype@) specification of a datatype: the refinement of
  each field is a conjunct of the contract of its constructor. A datatype
  without a @data@ specification has fields without refinements;
* abstract refinements of a @data@ specification, such as
  @data RBTree a \<l :: a -> a -> Bool, r :: a -> a -> Bool\>@, with the
  alias that instantiates them, such as
  @type ORBT a = RBTree \<{\\root v -> v \< root}, {\\root v -> v > root}\> a@.
  The built-in list has the abstract refinement of Liquid Haskell, as in
  @type OList a = [a]\<{\\fld v -> v >= fld}\>@;
* @measure@ specifications with their equations, which are named measures
  of the constructors. A measure gives an integer, a Boolean (as zero or
  one), or a constructor of a type whose constructors have no fields (as the
  position of the constructor);
* @type@ aliases with type and value parameters, and @predicate@ aliases.

A refinement of the elements of a child, as @tl :: IncList {v:a | hd <= v}@,
holds for every element of the child. The translation derives the least or
the greatest element of the child as a named measure, so the refinement is a
contract on that measure. A conjunction of linear order relations on @v@ has
an exact translation. When the target bounds the elements, an empty child has
the bound plus one as its least element, and an element that the contract
places below every element of a child is the least element of its node. So
the sorted lists above have the measure and the contract of the hand-written
generator of SortedLists.hs. Without a bound, a derived measure says whether a
child is empty.

A Boolean measure that the target requires at the root, and that holds
exactly when a condition holds at each node, becomes a contract: the measure
@isRB (Node c x l r) = isRB l && isRB r && local@ of a red-black tree gives
the contract @local@ to each @Node@, so the generator does not build the trees
where it fails.

A datatype with one measure has it as the measure of
'Data.CFTA.Gen.Refinement.measured', so its atomic fields can come from
'Data.CFTA.Gen.Refinement.every'. A datatype with several measures has named
measures, as 'Data.CFTA.Gen.Refinement.measuredBy' gives them, and each named
measure must be one integer for each tuple of children: its atomic fields
come from 'Data.CFTA.Gen.Refinement.elements' or a pool.

The translation is exact or it fails. It rejects, with 'Untranslatable' and
the position of the specification, each part that it cannot translate
exactly: a refinement of elements that is not a conjunction of linear order
relations, such as @v /= hd@; a measure of another sort, such as a set; a
measure that Liquid Haskell lifts from a Haskell function (@measure f@
without equations), an inlined or a reflected function; a name that is not
a field; and a product of two terms that are not constants. Other kinds of
specification, such as function signatures and invariants, do not change the
values of a datatype, and the translation ignores them.

The equations of a measure are indented more than the word @measure@, as
the layout rule of the Liquid Haskell parser requires. With the equations at
the column of @measure@, the parser reads an equation as a new
specification, and the error is "unexpected Em, expecting :: or ','".

Haddock text that shows a specification must not contain the two characters
that open a Haskell block comment (a left brace and a hyphen) or the two that
close it (a hyphen and a right brace): the first pair opens a nested comment,
and the second pair ends the comment. Escape the hyphen and the at sign with a
backslash, as the examples above do in the source of this module.
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
    Translation (..),
    liquidTranslation,
    deriveLTAFromLiquid,
    renderParseError,
) where

import Control.Monad (forM, forM_, guard, unless, when, zipWithM)
import Data.Bifunctor (bimap, first)
import Data.Either (lefts, rights)
import Data.List (find)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, isJust, listToMaybe, mapMaybe)
import Data.Proxy (Proxy (Proxy))
import qualified Data.Set as Set
import Data.String (fromString)
import qualified Data.Text as Text
import Data.Typeable (TypeRep, tyConName, typeRepTyCon)
import Text.Megaparsec.Pos (SourcePos (SourcePos), mkPos, unPos)
import qualified Text.PrettyPrint.HughesPJ as PJ

import qualified Language.Fixpoint.Types as F
import Language.Haskell.Liquid.Parse (BPspec (..), parseSpecComments)
import Language.Haskell.Liquid.Types.DataDecl (DataCtorP (..), DataDeclP (..), DataDeclParsed, DataName (..))
import Language.Haskell.Liquid.Types.Errors (ppError)
import Language.Haskell.Liquid.Types.Names (LHName, getLHNameSymbol)
import Language.Haskell.Liquid.Types.RType (
    BTyCon (..),
    BTyVar (..),
    BareTypeParsed,
    LocBareTypeParsed,
    PVarBV (..),
    PredicateBV (..),
    RTPropBV,
    RTypeBV (..),
    RefB (..),
    UReftBV (..),
 )
import Language.Haskell.Liquid.Types.Types (BodyV (..), DefV (..), Error, MeasureV (..), RTAlias (..))

import Data.CFTA.Formula (Relation (..), Term (..))
import qualified Data.CFTA.Formula as Formula
import Data.CFTA.Gen.Refinement (LTAGen, satisfying)
import Data.CFTA.Gen.Refinement.Derive (
    Annotation,
    Atoms,
    DeriveLTAError,
    deriveLTAWith,
    fieldsContract,
    fieldsMeasure,
    fieldsMeasureNamed,
 )
import Data.CFTA.Generic (Constructor (..), Description (..), HasFTA (..))
import Data.CFTA.Index (ArgumentIndex (..), Depth)
import Data.CFTA.Refinement (contractTermName)
import Data.CFTA.Refinement.Expression (
    Expr,
    Formula,
    Refinement,
    false,
    fromExpr,
    lnot,
    substitute,
    toExpr,
    true,
    uninterpreted,
    variable,
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
    | -- | The target is neither an alias nor a datatype that the type reaches.
      UnknownTarget !String
    | {- | A part of a specification that the translation cannot translate
      exactly. The fields are the place, with the position of the
      specification, and the reason.
      -}
      Untranslatable !String !String
    | -- | The derivation rejects the translated annotations.
      DerivationFailed !DeriveLTAError
    deriving (Eq, Show)

-- | The text of one error of the Liquid Haskell parser.
renderParseError :: Error -> String
renderParseError err = PJ.render $ ppError F.Full PJ.empty (PJ.empty <$ err)

{- | The translation of a target: the annotations of the constructors of the
datatypes that the target reaches, for 'deriveLTAWith', and the refinement of
the root, if the target has one.
-}
data Translation = Translation
    { translationAnnotations :: ![(String, Annotation)]
    , translationRoot :: !(Maybe Refinement)
    }

{- | Derive the refinement generator of a target from the Liquid Haskell
specifications. This is 'deriveLTAWith' with the annotations of
'liquidTranslation', and 'satisfying' with the refinement of the root. The
type is the datatype of the target at its element types, as
@IncList Integer@.
-}
deriveLTAFromLiquid ::
    forall a. (HasFTA a) => Depth -> Atoms -> Specifications -> String -> Either LiquidError (LTAGen a)
deriveLTAFromLiquid bound atoms specs target = do
    Translation annotations root <- liquidTranslation @a specs target
    generator <- first DerivationFailed $ deriveLTAWith @a bound atoms annotations
    pure $ maybe generator (generator `satisfying`) root

{- | Translate the specifications of a target: an alias without parameters,
or the name of a datatype. The type is the datatype of the target at its
element types.
-}
liquidTranslation :: forall a. (HasFTA a) => Specifications -> String -> Either LiquidError Translation
liquidTranslation specs target = do
    index <- indexOf =<< parseSpecifications specs
    let description = describeType (Proxy @a)
        reached = reach index description
    rootRep <- case description of
        AlgebraicType rep _ -> Right rep
        AtomicType rep -> Left $ Untranslatable target $ show rep <> " is an atomic type, without constructors"
    let rootName = lhNameOf rootRep
    (place, shape) <- targetShape index rootName target
    (instantiation, rootRefinements) <- case shape of
        Constructed name arguments properties refinements
            | name == rootName -> do
                instantiation <- instantiate index place (datatypeDeclaration =<< Map.lookup rootRep reached) arguments properties
                Right (instantiation, refinements)
            | otherwise ->
                Left $ Untranslatable place $ "the target is a " <> name <> ", and the type is a " <> rootName
        Variable{} -> Left $ Untranslatable place "the target is a type variable"
    checkConstructorNames reached
    let context = contextOf index reached
    rules <- fmap Map.fromList $ forM (Map.toList reached) $ \(rep, datatype) -> do
        let typeInstantiation = if rep == rootRep then instantiation else emptyInstantiation
        perConstructor <- forM (datatypeAlternatives datatype) $ \alternative ->
            (,) (constructorName $ fst alternative) <$> constructorRules context rep datatype typeInstantiation alternative
        Right (rep, perConstructor)
    let modes = summaryModes reached rootRep instantiation rules
        contracts =
            [ (name, contractOf modes constructorRules')
            | perConstructor <- Map.elems rules
            , (name, constructorRules') <- perConstructor
            ]
    rootFormula <-
        fmap Formula.conjunction $ forM rootRefinements $ \(binder, expression) ->
            formulaOf context place (Map.singleton (symbolName binder) (NodeValue rootRep rootTerm)) expression
    needed <- neededMeasures context modes rules (Set.unions $ appliedIn rootFormula : map (appliedIn . snd) contracts)
    let (rootConjunction, nodeContracts, measures) = localize reached rootRep (rootFormula, contracts, needed)
    -- A datatype with one measure that reads no other measure has it as the
    -- measure of 'measured', which also counts children from 'every'. A
    -- formula reads that measure of a child as the term of the child.
    let named = Map.fromListWith (<>) [(owner, [name]) | (owner, name) <- Map.keys measures]
        single =
            Set.fromList
                [ fromString name
                | (owner, [name]) <- Map.toList named
                , all
                    (\(_, term) -> appliedInTerm (fromExpr term) `Set.isSubsetOf` Set.singleton (fromString name))
                    (measures Map.! (owner, name))
                ]
        unnamed = unnameFormula single
        annotations =
            [ (name, contractPart <> measurePart)
            | (rep, datatype) <- Map.toList reached
            , (constructor, children) <- datatypeAlternatives datatype
            , let name = constructorName constructor
                  arity = length children
                  formula = unnamed $ fromMaybe Formula.Top $ lookup name nodeContracts
                  contractPart
                    | formula == Formula.Top = mempty
                    | otherwise = fieldsContract arity (const formula)
                  measurePart =
                    mconcat
                        [ if Set.member (fromString measureName) single
                            then fieldsMeasure arity (const term')
                            else fieldsMeasureNamed measureName arity (const term')
                        | ((owner, measureName), equations) <- Map.toList measures
                        , owner == rep
                        , Just term <- [lookup name equations]
                        , let term' = toExpr $ unnameTerm single $ fromExpr term
                        ]
            ]
        root
            | rootConjunction == Formula.Top = Nothing
            | otherwise = Just $ \value -> substitute [(rootVariable, value)] (unnamed rootConjunction)
    pure $ Translation annotations root

-- * The specifications by name

-- | The specifications that the translation reads, by name.
data Index = Index
    { indexDeclarations :: !(Map.Map String Declaration)
    , indexAliases :: !(Map.Map String (RTAlias F.Symbol BareTypeParsed))
    , indexPredicates :: !(Map.Map String (RTAlias F.Symbol (F.ExprV F.LocSymbol)))
    , indexMeasures :: !(Map.Map String LiquidMeasure)
    , indexOthers :: !(Map.Map String String)
    }

-- | A measure with its equations.
type LiquidMeasure = MeasureV F.LocSymbol LocBareTypeParsed (F.Located LHName)

{- | A @data@ specification: the type variables, the abstract refinements,
and the fields of each constructor by its Haskell name.
-}
data Declaration = Declaration
    { declarationVariables :: ![String]
    , declarationProperties :: ![String]
    , declarationConstructors :: !(Map.Map String (F.Located LHName, [(String, BareTypeParsed)]))
    }

-- | The specifications by name, with the built-in list.
indexOf :: [BPspec] -> Either LiquidError Index
indexOf parsed = do
    let declarations = [declaration | DDecl declaration <- parsed] <> [declaration | NTDecl declaration <- parsed]
        names = map dataNameOf declarations
    case [name | (name, count) <- Map.toList $ Map.fromListWith (+) [(name, 1 :: Int) | name <- names], count > 1] of
        name : _ -> Left $ Untranslatable name "there is more than one data specification"
        [] -> pure ()
    translated <- forM declarations $ \declaration -> (,) (dataNameOf declaration) <$> declarationOf id declaration
    pure
        Index
            { indexDeclarations = Map.fromList translated <> Map.singleton listName builtInList
            , indexAliases = Map.fromList [(nameOf $ F.val $ rtName alias, alias) | Alias alias <- parsed]
            , indexPredicates = Map.fromList [(nameOf $ F.val $ rtName alias, alias) | EAlias alias <- parsed]
            , indexMeasures = Map.fromList [(nameOf $ F.val $ msName measure', measure') | Meas measure' <- parsed]
            , indexOthers =
                Map.fromList $
                    [(nameOf $ F.val name, "a measure that Liquid Haskell lifts from a Haskell function") | HMeas name <- parsed]
                        <> [(nameOf $ F.val name, "an inlined Haskell function") | Inline name <- parsed]
                        <> [(nameOf $ F.val name, "a reflected Haskell function") | Reflect name <- parsed]
            }

-- | A @data@ specification, with the constructor names that the function gives.
declarationOf :: (String -> String) -> DataDeclParsed -> Either LiquidError Declaration
declarationOf rename declaration = do
    constructors <-
        maybe (Left $ Untranslatable (dataNameOf declaration) "the data specification has no constructors") Right $
            tycDCons declaration
    forM_ constructors $ \constructor ->
        when (isJust $ dcResult constructor)
            $ Left
            $ Untranslatable
                (placeOf (dcName constructor) $ "constructor " <> nameOf (F.val $ dcName constructor))
                "a constructor with a result type is not translated"
    pure
        Declaration
            { declarationVariables = map symbolName $ tycTyVars declaration
            , declarationProperties = [symbolName $ pname property | property <- tycPVars declaration]
            , declarationConstructors =
                Map.fromList
                    [ ( rename $ nameOf $ F.val $ dcName constructor
                      , (dcName constructor, [(nameOf field, typ) | (field, typ) <- dcFields constructor])
                      )
                    | constructor <- constructors
                    ]
            }

-- | The Liquid Haskell name of the built-in list type.
listName :: String
listName = "[]"

{- | The built-in list of Liquid Haskell, with its abstract refinement, as in
@(:) :: head:a -> tail:[a\<p head\>]\<p\> -> [a]\<p\>@.
-}
builtInList :: Declaration
builtInList = case parseSpecComments [(SourcePos "cfta-liquid" (mkPos 1) (mkPos 1), text)] of
    Right [DDecl declaration] | Right translated <- declarationOf rename declaration -> translated
    _ -> error "cfta-liquid bug: the declaration of the built-in list does not parse"
  where
    text = "data List a <p :: a -> a -> Bool> = Nil | Cons { head :: a, tail :: [a<p head>]<p> }"
    rename name = case name of
        "Nil" -> "[]"
        "Cons" -> ":"
        _ -> name

-- | The name of a Liquid Haskell name, without its qualification.
nameOf :: LHName -> String
nameOf = F.symbolString . getLHNameSymbol

-- | The name of a symbol.
symbolName :: F.Symbol -> String
symbolName = F.symbolString

-- | The name of the type of a data specification.
dataNameOf :: DataDeclP v ty -> String
dataNameOf declaration = case tycName declaration of
    DnName name -> nameOf $ F.val name
    DnCon name -> nameOf $ F.val name

-- | A place with the position of a located name.
placeOf :: F.Located a -> String -> String
placeOf located what =
    let SourcePos file line column = F.loc located
     in file <> ":" <> show (unPos line) <> ":" <> show (unPos column) <> ": " <> what

-- * Datatypes

{- | A datatype that the target reaches: its Liquid Haskell name, its
constructors with the descriptions of their fields, and its @data@
specification, if it has one.
-}
data Datatype = Datatype
    { datatypeName :: !String
    , datatypeAlternatives :: ![(Constructor, [Description])]
    , datatypeDeclaration :: !(Maybe Declaration)
    }

-- | Whether the constructors of a datatype have no fields.
isEnumeration :: Datatype -> Bool
isEnumeration datatype = all (null . snd) $ datatypeAlternatives datatype

-- | The datatypes with constructors that a description reaches.
reach :: Index -> Description -> Map.Map TypeRep Datatype
reach index = go Map.empty
  where
    go reached description = case description of
        AtomicType _ -> reached
        AlgebraicType rep alternatives
            | Map.member rep reached -> reached
            | otherwise ->
                let name = lhNameOf rep
                    datatype = Datatype name alternatives (Map.lookup name $ indexDeclarations index)
                 in foldl go (Map.insert rep datatype reached) (concatMap snd alternatives)

-- | The Liquid Haskell name of a Haskell type.
lhNameOf :: TypeRep -> String
lhNameOf rep = case tyConName $ typeRepTyCon rep of
    "List" -> listName
    "Unit" -> "Tuple0"
    name -> name

{- | Reject datatypes that share a constructor name: the annotations of
'deriveLTAWith' are by constructor name.
-}
checkConstructorNames :: Map.Map TypeRep Datatype -> Either LiquidError ()
checkConstructorNames reached =
    case [name | (name, count) <- Map.toList counts, count > (1 :: Int)] of
        name : _ -> Left $ Untranslatable name "two datatypes that the target reaches have a constructor with this name"
        [] -> Right ()
  where
    counts =
        Map.fromListWith
            (+)
            [(constructorName constructor, 1) | datatype <- Map.elems reached, (constructor, _) <- datatypeAlternatives datatype]

-- * Types

-- | A refinement: its value binder and its formula.
type Refined = (F.Symbol, F.ExprV F.LocSymbol)

-- | An application of an abstract refinement: its name and its arguments.
type Application = (String, [F.ExprV F.LocSymbol])

-- | An abstract refinement argument of a type, as in @\<{\\root v -> v \< root}\>@.
type PropertyArgument =
    RTPropBV F.Symbol F.LocSymbol BTyCon BTyVar (UReftBV F.Symbol F.LocSymbol (F.ReftBV F.Symbol F.LocSymbol))

-- | A type after the expansion of its aliases.
data Shape
    = -- | A type constructor with its type arguments, its abstract refinement arguments, and its refinements.
      Constructed !String ![BareTypeParsed] ![PropertyArgument] ![Refined]
    | -- | A type variable with its refinements and its applications of abstract refinements.
      Variable !String ![Refined] ![Application]

-- | The shape of a type: its aliases expanded, and their refinements collected.
shapeOf :: Index -> String -> BareTypeParsed -> Either LiquidError Shape
shapeOf index place = go (16 :: Int)
  where
    go depth typ = case typ of
        RVar (BTV name) reft -> Right $ Variable (symbolName $ F.val name) (refinementsOf reft) (applicationsOf reft)
        RApp{rt_tycon, rt_args, rt_pargs, rt_reft}
            | Just alias <- Map.lookup (tyConNameOf rt_tycon) (indexAliases index) -> do
                when (depth <= 0) $ Left $ Untranslatable place "the aliases expand more than sixteen times"
                let typeArguments = [argument | argument <- rt_args, not (isExpression argument)]
                    valueArguments = [F.val expression | RExprArg expression <- rt_args]
                    aliasPlace = placeOf (rtName alias) ("the alias " <> nameOf (F.val $ rtName alias))
                unless (length typeArguments == length (rtTArgs alias) && length valueArguments == length (rtVArgs alias))
                    $ Left
                    $ Untranslatable aliasPlace
                    $ "the alias takes "
                        <> show (length $ rtTArgs alias)
                        <> " types and "
                        <> show (length $ rtVArgs alias)
                        <> " values"
                unless (null rt_pargs)
                    $ Left
                    $ Untranslatable aliasPlace "an alias with abstract refinement arguments is not translated"
                unless (null $ applicationsOf rt_reft)
                    $ Left
                    $ Untranslatable place "an abstract refinement of an alias is not translated"
                let body =
                        substituteType
                            (Map.fromList $ zip (map symbolName $ rtTArgs alias) typeArguments)
                            (Map.fromList $ zip (map symbolName $ rtVArgs alias) valueArguments)
                            (rtBody alias)
                shape <- go (depth - 1) body
                Right $ strengthen shape (refinementsOf rt_reft)
            | otherwise -> do
                unless (null $ applicationsOf rt_reft)
                    $ Left
                    $ Untranslatable place "an abstract refinement of a type constructor is not translated"
                Right $ Constructed (tyConNameOf rt_tycon) rt_args rt_pargs (refinementsOf rt_reft)
        _ -> Left $ Untranslatable place "only a type constructor or a type variable is translated"
    isExpression RExprArg{} = True
    isExpression _ = False
    strengthen shape refinements = case shape of
        Constructed name arguments properties own -> Constructed name arguments properties (own <> refinements)
        Variable name own applications -> Variable name (own <> refinements) applications

-- | The name of a type constructor.
tyConNameOf :: BTyCon -> String
tyConNameOf = nameOf . F.val . btc_tc

-- | The refinements of a refinement, without the trivial one.
refinementsOf :: UReftBV F.Symbol F.LocSymbol (F.ReftBV F.Symbol F.LocSymbol) -> [Refined]
refinementsOf (MkUReft (F.Reft (binder, expression)) _) = case expression of
    F.PAnd [] -> []
    _ -> [(binder, expression)]

-- | The applications of abstract refinements in a refinement.
applicationsOf :: UReftBV F.Symbol F.LocSymbol r -> [Application]
applicationsOf (MkUReft _ (Pr properties)) =
    [(symbolName $ pname property, [argument | (_, _, argument) <- pargs property]) | property <- properties]

{- | Replace the type variables and the value parameters of an alias body by
the arguments.
-}
substituteType ::
    Map.Map String BareTypeParsed -> Map.Map String (F.ExprV F.LocSymbol) -> BareTypeParsed -> BareTypeParsed
substituteType types values = go
  where
    go typ = case typ of
        RVar (BTV name) reft
            | Just replacement <- Map.lookup (symbolName $ F.val name) types -> strengthenType (refine reft) replacement
            | otherwise -> RVar (BTV name) (refine reft)
        RApp tycon arguments properties reft -> RApp tycon (map go arguments) (map property properties) (refine reft)
        RExprArg expression -> RExprArg (substituteExpression values <$> expression)
        RHole reft -> RHole (refine reft)
        _ -> typ
    property (RProp arguments body) = RProp arguments (go body)
    refine (MkUReft (F.Reft (binder, expression)) predicate) =
        MkUReft (F.Reft (binder, substituteExpression (Map.delete (symbolName binder) values) expression)) predicate

-- | Add a refinement to the outermost refinement of a type.
strengthenType :: UReftBV F.Symbol F.LocSymbol (F.ReftBV F.Symbol F.LocSymbol) -> BareTypeParsed -> BareTypeParsed
strengthenType extra typ = case typ of
    RVar name reft -> RVar name (combine reft)
    RApp tycon arguments properties reft -> RApp tycon arguments properties (combine reft)
    _ -> typ
  where
    MkUReft (F.Reft (extraBinder, extraExpression)) (Pr extraProperties) = extra
    combine (MkUReft (F.Reft (binder, expression)) (Pr properties)) =
        let renamed = substituteExpression (Map.singleton (symbolName extraBinder) (F.EVar $ F.dummyLoc binder)) extraExpression
         in MkUReft (F.Reft (binder, conjoin expression renamed)) (Pr $ properties <> extraProperties)
    conjoin (F.PAnd []) right = right
    conjoin left (F.PAnd []) = left
    conjoin left right = F.PAnd [left, right]

-- | Replace the named variables of an expression.
substituteExpression :: Map.Map String (F.ExprV F.LocSymbol) -> F.ExprV F.LocSymbol -> F.ExprV F.LocSymbol
substituteExpression replacements
    | Map.null replacements = id
    | otherwise = go
  where
    go expression = case expression of
        F.EVar name -> fromMaybe expression $ Map.lookup (symbolName $ F.val name) replacements
        F.EApp function argument -> F.EApp (go function) (go argument)
        F.ENeg inner -> F.ENeg (go inner)
        F.EBin operator left right -> F.EBin operator (go left) (go right)
        F.EIte condition yes no -> F.EIte (go condition) (go yes) (go no)
        F.ECst inner sort -> F.ECst (go inner) sort
        F.PAnd parts -> F.PAnd (map go parts)
        F.POr parts -> F.POr (map go parts)
        F.PNot inner -> F.PNot (go inner)
        F.PImp left right -> F.PImp (go left) (go right)
        F.PIff left right -> F.PIff (go left) (go right)
        F.PAtom relation left right -> F.PAtom relation (go left) (go right)
        _ -> expression

-- | The shape of a target: an alias without parameters, or a datatype.
targetShape :: Index -> String -> String -> Either LiquidError (String, Shape)
targetShape index rootName target = case Map.lookup target (indexAliases index) of
    Just alias -> do
        let place = placeOf (rtName alias) ("the target " <> target)
        unless (null (rtTArgs alias) && null (rtVArgs alias)) $ Left $ Untranslatable place "the target alias has parameters"
        (,) place <$> shapeOf index place (rtBody alias)
    Nothing
        | target == rootName || Map.member target (indexDeclarations index) -> Right (target, Constructed target [] [] [])
        | otherwise -> Left $ UnknownTarget target

-- | The refinements of the type variables and the abstract refinements of the target.
data Instantiation = Instantiation
    { instantiationVariables :: !(Map.Map String [Refined])
    , instantiationProperties :: !(Map.Map String Property)
    }

-- | An abstract refinement: its parameters, its value binder, and its formula.
data Property = Property ![String] !F.Symbol !(F.ExprV F.LocSymbol)

-- | No refinements.
emptyInstantiation :: Instantiation
emptyInstantiation = Instantiation Map.empty Map.empty

{- | The refinements that the arguments of the target give to the type
variables and the abstract refinements of its datatype. An abstract
refinement without an argument is true, as in Liquid Haskell.
-}
instantiate ::
    Index -> String -> Maybe Declaration -> [BareTypeParsed] -> [PropertyArgument] -> Either LiquidError Instantiation
instantiate index place declared arguments properties = case declared of
    Nothing -> do
        shapes <- traverse (shapeOf index place) arguments
        if all trivialShape shapes && null properties
            then Right emptyInstantiation
            else Left $ Untranslatable place "the datatype has no data specification for the refinements of its arguments"
    Just declaration -> do
        unless (null arguments || length arguments == length (declarationVariables declaration))
            $ Left
            $ Untranslatable place
            $ "the datatype takes " <> show (length $ declarationVariables declaration) <> " types"
        unless (null properties || length properties == length (declarationProperties declaration))
            $ Left
            $ Untranslatable place
            $ "the datatype takes " <> show (length $ declarationProperties declaration) <> " abstract refinements"
        variables <- forM (zip (declarationVariables declaration) arguments) $ \(name, argument) -> do
            shape <- shapeOf index place argument
            case shape of
                Variable _ refinements [] -> Right (name, refinements)
                Constructed _ inner [] refinements | all trivialArgument inner -> Right (name, refinements)
                _ -> Left $ Untranslatable place $ "the refinements inside the argument for " <> name <> " are not translated"
        lambdas <- forM (zip (declarationProperties declaration) properties) $ \(name, RProp parameters body) ->
            case [refined | RVar _ reft <- [body], refined <- refinementsOf reft]
                <> [refined | RHole reft <- [body], refined <- refinementsOf reft] of
                [(binder, expression)] -> Right (name, Property [symbolName parameter | (parameter, _) <- parameters] binder expression)
                _ -> Left $ Untranslatable place $ "the abstract refinement " <> name <> " is not a refinement of its value"
        Right $ Instantiation (Map.fromList variables) (Map.fromList lambdas)
  where
    trivialShape shape = case shape of
        Variable _ [] [] -> True
        Constructed _ inner [] [] -> all trivialArgument inner
        _ -> False
    trivialArgument argument = case argument of
        RApp _ inner _ reft -> null (refinementsOf reft) && all trivialArgument inner
        RVar _ reft -> null (refinementsOf reft)
        _ -> False

-- * Values

-- | The value of an expression: a term, a formula, or a value of a datatype with constructors.
data Value
    = TermValue !Expr
    | TruthValue !Formula
    | NodeValue !TypeRep !Expr

-- | What an evaluation reads: the specifications and the datatypes.
data Context = Context
    { contextIndex :: !Index
    , contextTypes :: !(Map.Map TypeRep Datatype)
    , contextNames :: !(Map.Map String TypeRep)
    , contextConstants :: !(Map.Map String (TypeRep, Integer))
    }

-- | The context of the datatypes that the target reaches.
contextOf :: Index -> Map.Map TypeRep Datatype -> Context
contextOf index reached =
    Context
        { contextIndex = index
        , contextTypes = reached
        , contextNames = Map.fromList [(datatypeName datatype, rep) | (rep, datatype) <- Map.toList reached]
        , contextConstants =
            Map.fromList
                [ (constructorName constructor, (rep, position))
                | (rep, datatype) <- Map.toList reached
                , isEnumeration datatype
                , (position, (constructor, _)) <- zip [0 ..] (datatypeAlternatives datatype)
                ]
        }

-- | The name of the root value in the formula of the root.
rootVariable :: String
rootVariable = "cftaRoot"

-- | The root value.
rootTerm :: Expr
rootTerm = variable rootVariable

-- | The name of an element in the refinement of the elements of a child.
elementVariable :: String
elementVariable = "cftaElement"

-- | The term of a field, as a contract names it.
fieldTerm :: Int -> Expr
fieldTerm position = variable $ contractTermName $ ArgumentIndex position

-- | The value of a field: a term for an atomic field, and a node for a field with constructors.
fieldValue :: Int -> Description -> Value
fieldValue position description = case description of
    AtomicType _ -> TermValue $ fieldTerm position
    AlgebraicType rep _ -> NodeValue rep $ fieldTerm position

-- | Evaluate an expression in an environment of named values.
evaluate :: Context -> String -> Map.Map String Value -> F.ExprV F.LocSymbol -> Either LiquidError Value
evaluate context place environment = go
  where
    fail' = Left . Untranslatable place
    go expression = case expression of
        F.ECon (F.I value) -> Right $ TermValue $ fromInteger value
        F.EVar name -> named (symbolName $ F.val name)
        F.EApp{} -> case spine expression [] of
            (F.EVar function, arguments) -> apply (symbolName $ F.val function) arguments
            _ -> fail' $ "the application " <> show expression <> " is not translated"
        F.ENeg inner -> TermValue . negate <$> term inner
        F.EBin F.Plus left right -> (\l r -> TermValue $ l + r) <$> term left <*> term right
        F.EBin F.Minus left right -> (\l r -> TermValue $ l - r) <$> term left <*> term right
        F.EBin F.Times left@(F.ECon _) right -> (\l r -> TermValue $ l * r) <$> term left <*> term right
        F.EBin F.Times left right@(F.ECon _) -> (\l r -> TermValue $ l * r) <$> term left <*> term right
        F.EBin F.Times _ _ -> fail' "a product of two terms that are not constants is not linear"
        F.EBin operator _ _ -> fail' $ "the operator " <> show operator <> " is not translated"
        F.EIte condition yes no -> do
            test <- formula condition
            yesValue <- go yes
            noValue <- go no
            case (yesValue, noValue) of
                (TruthValue a, TruthValue b) -> Right $ TruthValue $ (test .&& a) .|| (lnot test .&& b)
                _ -> (\a b -> TermValue $ toExpr $ Ite test (fromExpr a) (fromExpr b)) <$> asTerm yesValue <*> asTerm noValue
        F.ECst inner _ -> go inner
        F.PAnd [] -> Right $ TruthValue true
        F.POr [] -> Right $ TruthValue false
        F.PAnd parts -> TruthValue . Formula.conjunction <$> traverse formula parts
        F.POr parts -> TruthValue . Formula.disjunction <$> traverse formula parts
        F.PNot inner -> TruthValue . lnot <$> formula inner
        F.PImp left right -> (\l r -> TruthValue $ lnot l .|| r) <$> formula left <*> formula right
        F.PIff left right -> (\l r -> TruthValue $ iff l r) <$> formula left <*> formula right
        F.PAtom relation left right -> do
            leftValue <- go left
            rightValue <- go right
            case (leftValue, rightValue) of
                (TruthValue l, TruthValue r)
                    | relation `elem` [F.Eq, F.Ueq] -> Right $ TruthValue $ iff l r
                    | relation `elem` [F.Ne, F.Une] -> Right $ TruthValue $ lnot $ iff l r
                _ -> do
                    l <- asTerm leftValue
                    r <- asTerm rightValue
                    Right $ TruthValue $ compare' relation l r
        _ -> fail' $ "the expression " <> show expression <> " is not translated"
    term expression = go expression >>= asTerm
    formula expression = go expression >>= asFormula
    spine (F.EApp function argument) arguments = spine function (argument : arguments)
    spine function arguments = (function, arguments)
    iff l r = (l .&& r) .|| (lnot l .&& lnot r)
    compare' relation = case relation of
        F.Eq -> (.==)
        F.Ueq -> (.==)
        F.Ne -> (./=)
        F.Une -> (./=)
        F.Lt -> (.<)
        F.Le -> (.<=)
        F.Gt -> (.>)
        F.Ge -> (.>=)
    named name
        | Just value <- Map.lookup name environment = Right value
        | Just (_, position) <- Map.lookup name (contextConstants context) = Right $ TermValue $ fromInteger position
        | Just alias <- Map.lookup name (indexPredicates $ contextIndex context)
        , null (rtVArgs alias) =
            evaluate context place Map.empty (rtBody alias)
        | otherwise = unknown name
    apply name arguments
        | Just alias <- Map.lookup name (indexPredicates $ contextIndex context) = do
            unless (length arguments == length (rtVArgs alias))
                $ fail'
                $ "the predicate " <> name <> " takes " <> show (length $ rtVArgs alias) <> " arguments"
            values <- traverse go arguments
            evaluate context place (Map.fromList $ zip (map symbolName $ rtVArgs alias) values) (rtBody alias)
        | Just measure' <- Map.lookup name (indexMeasures $ contextIndex context) = case arguments of
            [argument] -> do
                value <- go argument
                case value of
                    NodeValue rep node
                        | Just datatype <- Map.lookup rep (contextTypes context)
                        , measureInput measure' == Just (datatypeName datatype) -> do
                            sort <- measureSort context measure'
                            let applied = uninterpreted name [node]
                            Right $ case sort of
                                BooleanSort -> TruthValue $ applied .== 1
                                _ -> TermValue applied
                    _ -> fail' $ "the measure " <> name <> " is applied to " <> show argument <> ", which is not a value of its datatype"
            _ -> fail' $ "the measure " <> name <> " is applied to " <> show (length arguments) <> " arguments"
        | otherwise = unknown name
    unknown name = case Map.lookup name (indexOthers $ contextIndex context) of
        Just kind -> fail' $ name <> " is " <> kind <> ", and the translation reads the equations of a measure in its specification"
        Nothing -> fail' $ name <> " is not a field, a measure, or a predicate"
    asTerm value = case value of
        TermValue t -> Right t
        NodeValue rep node
            | Just datatype <- Map.lookup rep (contextTypes context)
            , isEnumeration datatype ->
                Right $ uninterpreted (enumerationMeasure rep) [node]
            | otherwise -> fail' $ "a value of " <> lhNameOf rep <> " is read through a measure"
        TruthValue _ -> fail' "a formula is not a term"
    asFormula value = case value of
        TruthValue f -> Right f
        _ -> fail' "a term is not a formula"

-- | Evaluate a formula.
formulaOf :: Context -> String -> Map.Map String Value -> F.ExprV F.LocSymbol -> Either LiquidError Formula
formulaOf context place environment expression = do
    value <- evaluate context place environment expression
    case value of
        TruthValue f -> Right f
        _ -> Left $ Untranslatable place $ "the refinement " <> show expression <> " is a term, not a formula"

-- | The sort of the value of a measure.
data MeasureSort = IntegerSort | BooleanSort | EnumerationSort

-- | The name of the type that a measure takes, as in @bh :: RBTree a -> Int@.
measureInput :: LiquidMeasure -> Maybe String
measureInput measure' = case F.val $ msSort measure' of
    RFun{rt_in = RApp{rt_tycon}} -> Just $ tyConNameOf rt_tycon
    _ -> Nothing

-- | The sort of the value of a measure: an integer, a Boolean, or a constructor of an enumeration.
measureSort :: Context -> LiquidMeasure -> Either LiquidError MeasureSort
measureSort context measure' = case F.val $ msSort measure' of
    RFun{rt_out = RApp{rt_tycon}}
        | name `elem` ["Int", "Integer", "Nat"] -> Right IntegerSort
        | name == "Bool" -> Right BooleanSort
        | Just rep <- Map.lookup name (contextNames context)
        , Just datatype <- Map.lookup rep (contextTypes context)
        , isEnumeration datatype ->
            Right EnumerationSort
        | otherwise -> unsupported $ "the measure gives a " <> name <> "; a measure of a liquid tree automaton is an integer"
      where
        name = tyConNameOf rt_tycon
    _ -> unsupported "the measure has a sort that is not a function from a datatype to a value"
  where
    unsupported = Left . Untranslatable (placeOf (msName measure') ("the measure " <> nameOf (F.val $ msName measure')))

-- | The named measure of the position of a constructor of an enumeration.
enumerationMeasure :: TypeRep -> String
enumerationMeasure rep = "cfta_constructor_" <> tyConName (typeRepTyCon rep)

-- * The rules of a constructor

-- | A side of a bound on the elements of a child.
data Side = Lower | Upper | Equal
    deriving (Eq, Show)

{- | A bound on the elements of a child: @coefficient * v@ against a term,
for each element @v@ of the child.
-}
data Bound = Bound
    { boundChild :: !Int
    , boundKey :: !SummaryKey
    , boundSide :: !Side
    , boundStrict :: !Bool
    , boundCoefficient :: !Integer
    , boundTerm :: !Expr
    , boundElement :: !(Maybe Int)
    }

-- | The datatype of a child and the position of a type variable: the elements that a derived measure reads.
type SummaryKey = (TypeRep, Int)

-- | The contract of a constructor, as conjuncts and bounds, and the fields that its derived measures read.
data Rules = Rules
    { rulesConjuncts :: ![Formula]
    , rulesBounds :: ![Bound]
    , rulesElements :: !(Map.Map String [Int])
    , rulesChildren :: ![(Int, TypeRep, [Maybe String])]
    , rulesType :: !TypeRep
    }

{- | The contract of a constructor: the refinements of its fields, and the
bounds on the elements of its children.
-}
constructorRules ::
    Context -> TypeRep -> Datatype -> Instantiation -> (Constructor, [Description]) -> Either LiquidError Rules
constructorRules context rep datatype instantiation (constructor, children) = case datatypeDeclaration datatype of
    Nothing -> Right $ Rules [] [] Map.empty [] rep
    Just declaration -> do
        (located, fields) <-
            maybe (Left $ Untranslatable (datatypeName datatype) $ "the data specification has no constructor " <> name) Right $
                Map.lookup name (declarationConstructors declaration)
        let place what = placeOf located (what <> " of " <> name)
        unless (length fields == arity)
            $ Left
            $ Untranslatable (place "the constructor")
            $ "the specification has " <> show (length fields) <> " fields, and the datatype has " <> show arity
        let values = zipWith fieldValue [0 ..] children
            environment = Map.fromList $ zip (map fst fields) values
        parts <- zipWithM (fieldRules declaration place environment) [0 ..] (zip3 fields children values)
        Right
            Rules
                { rulesConjuncts = concat [formulas | (formulas, _, _, _) <- parts]
                , rulesBounds = concat [bounds | (_, bounds, _, _) <- parts]
                , rulesElements =
                    Map.fromListWith (flip (<>)) [(variableName, [position]) | (_, _, Just (variableName, position), _) <- parts]
                , rulesChildren = [child | (_, _, _, Just child) <- parts]
                , rulesType = rep
                }
  where
    name = constructorName constructor
    arity = length children
    fieldRules declaration place environment position ((field, typ), description, value) = do
        let fieldPlace = place ("field " <> field)
            refined (binder, expression) =
                formulaOf context fieldPlace (Map.insert (symbolName binder) value environment) expression
        shape <- shapeOf (contextIndex context) fieldPlace typ
        case shape of
            Variable variableName refinements applications -> do
                own <- traverse refined refinements
                instantiated <- traverse refined $ Map.findWithDefault [] variableName (instantiationVariables instantiation)
                applied <- traverse (propertyFormula fieldPlace environment value) applications
                Right (own <> instantiated <> concat applied, [], Just (variableName, position), Nothing)
            Constructed childName arguments properties refinements -> do
                own <- traverse refined refinements
                (elementConjuncts, bounds, child) <- case description of
                    AlgebraicType childRep _
                        | Just childType <- Map.lookup childRep (contextTypes context)
                        , datatypeName childType == childName -> do
                            checkProperties fieldPlace childRep childType properties
                            childVariables <- forM arguments $ \argument -> do
                                argumentShape <- shapeOf (contextIndex context) fieldPlace argument
                                Right $ case argumentShape of
                                    Variable variableName _ _ -> Just variableName
                                    Constructed{} -> Nothing
                            perArgument <- forM (zip [0 ..] arguments) $ \(argumentPosition, argument) ->
                                elementRules fieldPlace environment position (childRep, argumentPosition) argument
                            Right
                                (concat [c | (c, _) <- perArgument], concat [b | (_, b) <- perArgument], Just (position, childRep, childVariables))
                    _
                        | null arguments && null properties -> Right ([], [], Nothing)
                        | otherwise ->
                            Left
                                $ Untranslatable fieldPlace
                                $ "the field is a " <> childName <> " with arguments, and the datatype has no such field"
                Right (own <> elementConjuncts, bounds, Nothing, child)
      where
        checkProperties fieldPlace childRep childType properties
            | childRep == rep
            , map passedName properties == map Just (declarationProperties declaration) =
                Right ()
            | childRep == rep
            , null properties
            , Map.null (instantiationProperties instantiation) =
                Right ()
            | childRep /= rep
            , null properties =
                Right ()
            | otherwise =
                Left
                    $ Untranslatable fieldPlace
                    $ "the abstract refinements of the " <> datatypeName childType <> " are not those of its datatype"
    passedName (RProp [] (RHole reft)) | [(property, [])] <- applicationsOf reft = Just property
    passedName _ = Nothing
    -- The formulas of the abstract refinements that a type variable applies.
    propertyFormula fieldPlace environment value (property, arguments) = case Map.lookup property (instantiationProperties instantiation) of
        Nothing -> Right []
        Just (Property parameters binder body) -> do
            unless (length parameters == length arguments)
                $ Left
                $ Untranslatable fieldPlace
                $ "the abstract refinement " <> property <> " takes " <> show (length parameters) <> " arguments"
            values <- traverse (evaluate context fieldPlace environment) arguments
            f <- formulaOf context fieldPlace (Map.insert (symbolName binder) value $ Map.fromList $ zip parameters values) body
            Right [f]
    -- The refinement of the elements of a child, as conjuncts without the
    -- element and bounds on the elements.
    elementRules fieldPlace environment child key argument = do
        argumentShape <- shapeOf (contextIndex context) fieldPlace argument
        let element = TermValue $ variable elementVariable
        formulas <- case argumentShape of
            Variable _ refinements applications -> do
                own <- forM refinements $ \(binder, expression) ->
                    formulaOf context fieldPlace (Map.insert (symbolName binder) element environment) expression
                applied <- traverse (propertyFormula fieldPlace environment element) applications
                Right $ own <> concat applied
            Constructed _ [] [] refinements ->
                forM refinements $ \(binder, expression) ->
                    formulaOf context fieldPlace (Map.insert (symbolName binder) element environment) expression
            Constructed{} -> Left $ Untranslatable fieldPlace "the refinements of nested element types are not translated"
        parts <- traverse (elementPart fieldPlace child key) (concatMap conjuncts formulas)
        Right (concat (lefts parts), rights parts)
    elementPart fieldPlace child key part
        | not (mentionsElement part) = Right $ Left [part]
        | Formula.Atom relation left right <- part
        , Just (leftCoefficient, leftRest) <- linear left
        , Just (rightCoefficient, rightRest) <- linear right =
            -- The atom is coefficient * v against tau, with a positive coefficient.
            let coefficient = leftCoefficient - rightCoefficient
                (relation', positive, tau)
                    | coefficient > 0 = (relation, coefficient, tidy $ Sub rightRest leftRest)
                    | otherwise = (flipRelation relation, negate coefficient, tidy $ Sub leftRest rightRest)
             in case (coefficient, sideOf relation') of
                    (0, _) -> Right $ Left [part]
                    (_, Nothing) -> Left $ Untranslatable fieldPlace "a refinement of elements that says v /= x needs the set of the elements"
                    (_, Just (side, strict)) ->
                        Right $
                            Right
                                Bound
                                    { boundChild = child
                                    , boundKey = key
                                    , boundSide = side
                                    , boundStrict = strict
                                    , boundCoefficient = positive
                                    , boundTerm = toExpr tau
                                    , boundElement = listToMaybe [field | field <- [0 .. arity - 1], tau == fromExpr (fieldTerm field)]
                                    }
        | otherwise =
            Left $ Untranslatable fieldPlace "the refinement of the elements is not a conjunction of linear order relations on v"
    -- The side of a bound, and whether it is strict.
    sideOf relation = case relation of
        Ge -> Just (Lower, False)
        Gt -> Just (Lower, True)
        Le -> Just (Upper, False)
        Lt -> Just (Upper, True)
        Eq -> Just (Equal, False)
        Ne -> Nothing

-- | The item at a position of a list.
at :: Int -> [a] -> Maybe a
at position items = case drop position items of
    item : _ | position >= 0 -> Just item
    _ -> Nothing

-- | The conjuncts of a formula, with negated relations as relations.
conjuncts :: Formula -> [Formula]
conjuncts formula = case formula of
    Formula.And parts -> concatMap conjuncts parts
    Formula.Top -> []
    Formula.Not (Formula.Atom relation left right) -> [Formula.Atom (negateRelation relation) left right]
    _ -> [formula]

-- | The relation that holds when the given one does not.
negateRelation :: Relation -> Relation
negateRelation relation = case relation of
    Eq -> Ne
    Ne -> Eq
    Lt -> Ge
    Ge -> Lt
    Le -> Gt
    Gt -> Le

-- | The relation with its sides swapped.
flipRelation :: Relation -> Relation
flipRelation relation = case relation of
    Lt -> Gt
    Gt -> Lt
    Le -> Ge
    Ge -> Le
    _ -> relation

-- | Whether a formula names the element.
mentionsElement :: Formula -> Bool
mentionsElement formula = fromString elementVariable `elem` Formula.freeNames formula

-- | The coefficient of the element in a term, and the term without the element, if the term is linear in the element.
linear :: Term -> Maybe (Integer, Term)
linear term = case term of
    Var name | name == fromString elementVariable -> Just (1, Lit 0)
    _ | fromString elementVariable `notElem` Formula.freeNames (Formula.Atom Eq term (Lit 0)) -> Just (0, term)
    Neg inner -> bimap negate Neg <$> linear inner
    Add left right -> (\(a, l) (b, r) -> (a + b, Add l r)) <$> linear left <*> linear right
    Sub left right -> (\(a, l) (b, r) -> (a - b, Sub l r)) <$> linear left <*> linear right
    Mul (Lit factor) inner -> bimap (factor *) (Mul (Lit factor)) <$> linear inner
    Mul inner (Lit factor) -> bimap (factor *) (`Mul` Lit factor) <$> linear inner
    _ -> Nothing

-- | Remove the zeros that 'linear' leaves.
tidy :: Term -> Term
tidy term = case term of
    Add left right -> case (tidy left, tidy right) of
        (Lit 0, r) -> r
        (l, Lit 0) -> l
        (l, r) -> Add l r
    Sub left right -> case (tidy left, tidy right) of
        (l, Lit 0) -> l
        (Lit 0, r) -> Neg r
        (l, r) -> Sub l r
    Neg inner -> case tidy inner of
        Lit value -> Lit (negate value)
        Neg twice -> twice
        other -> Neg other
    Mul left right -> Mul (tidy left) (tidy right)
    _ -> term

-- * Derived measures

-- | How a derived measure stands for an empty child.
data Mode
    = -- | The bound beyond the elements: the least element of an empty child is the greatest bound plus one.
      Sentinel !(Maybe Integer) !(Maybe Integer)
    | -- | A named measure says whether the child has no elements.
      Flag

-- | A derived measure: the least element, the greatest element, or whether there are no elements.
data Summary = Least | Greatest | Empty
    deriving (Eq, Ord, Show)

-- | The name of a derived measure.
summaryMeasure :: Summary -> SummaryKey -> String
summaryMeasure summary (rep, position) =
    "cfta_" <> kind <> "_" <> tyConName (typeRepTyCon rep) <> "_" <> show position
  where
    kind = case summary of
        Least -> "least"
        Greatest -> "greatest"
        Empty -> "empty"

{- | The mode of each derived measure. The bound of the elements is plus one
past their greatest value (for the least element) and minus one past their
least value (for the greatest). The bound stands for an empty child only when
each bound on these elements compares them with an element of the same node:
then the element lies inside the bounds, and the comparison with an empty
child holds.
-}
summaryModes ::
    Map.Map TypeRep Datatype -> TypeRep -> Instantiation -> Map.Map TypeRep [(String, Rules)] -> Map.Map SummaryKey Mode
summaryModes reached rootRep instantiation rules =
    Map.fromList [(key, modeOf key bounds) | (key, bounds) <- Map.toList grouped]
  where
    grouped =
        Map.fromListWith
            (<>)
            [ (boundKey bound, [(constructorRules', bound)])
            | perConstructor <- Map.elems rules
            , (_, constructorRules') <- perConstructor
            , bound <- rulesBounds constructorRules'
            ]
    modeOf (rep, position) bounds
        | rep == rootRep
        , Just variableName <- variableAt rep position
        , all (sentinelBound rep variableName) bounds
        , (lower, upper) <- literalBounds $ Map.findWithDefault [] variableName (instantiationVariables instantiation)
        , not (any ((== Lower) . boundSide . snd) bounds) || isJust upper
        , not (any ((== Upper) . boundSide . snd) bounds) || isJust lower =
            Sentinel lower upper
        | otherwise = Flag
    -- A bound that compares the elements with an element of the same node.
    sentinelBound rep variableName (owner, bound) =
        rulesType owner == rep
            && boundCoefficient bound == 1
            && boundSide bound /= Equal
            && maybe False (`elem` Map.findWithDefault [] variableName (rulesElements owner)) (boundElement bound)
    variableAt rep position = Map.lookup rep reached >>= datatypeDeclaration >>= \declaration -> at position (declarationVariables declaration)

{- | The least and the greatest value that a list of refinements allows, from
their conjuncts of the form @v >= 0@ and @v \< 10@.
-}
literalBounds :: [Refined] -> (Maybe Integer, Maybe Integer)
literalBounds refinements = (maximum' lowers, minimum' uppers)
  where
    atoms = concatMap (uncurry atomBounds) refinements
    lowers = [value | (Lower, value) <- atoms]
    uppers = [value | (Upper, value) <- atoms]
    maximum' values = if null values then Nothing else Just (maximum values)
    minimum' values = if null values then Nothing else Just (minimum values)
    atomBounds binder expression = case expression of
        F.PAnd parts -> concatMap (atomBounds binder) parts
        F.PAtom relation (F.EVar name) (F.ECon (F.I value)) | F.val name == binder -> side relation value
        F.PAtom relation (F.ECon (F.I value)) (F.EVar name) | F.val name == binder -> side (flipFixpoint relation) value
        _ -> []
    side relation value = case relation of
        F.Ge -> [(Lower, value)]
        F.Gt -> [(Lower, value + 1)]
        F.Le -> [(Upper, value)]
        F.Lt -> [(Upper, value - 1)]
        F.Eq -> [(Lower, value), (Upper, value)]
        _ -> []
    flipFixpoint relation = case relation of
        F.Ge -> F.Le
        F.Gt -> F.Lt
        F.Le -> F.Ge
        F.Lt -> F.Gt
        _ -> relation

-- | The contract of a constructor, with the bounds on the derived measures of its children.
contractOf :: Map.Map SummaryKey Mode -> Rules -> Formula
contractOf modes constructorRules' =
    Formula.conjunction $ rulesConjuncts constructorRules' <> map boundFormula (rulesBounds constructorRules')
  where
    boundFormula bound =
        let key = boundKey bound
            child = fieldTerm (boundChild bound)
            scaled summary
                | boundCoefficient bound == 1 = uninterpreted (summaryMeasure summary key) [child]
                | otherwise = fromInteger (boundCoefficient bound) * uninterpreted (summaryMeasure summary key) [child]
            tau = boundTerm bound
            compared = case (boundSide bound, boundStrict bound) of
                (Lower, False) -> scaled Least .>= tau
                (Lower, True) -> scaled Least .> tau
                (Upper, False) -> scaled Greatest .<= tau
                (Upper, True) -> scaled Greatest .< tau
                (Equal, _) -> scaled Least .== tau .&& scaled Greatest .== tau
         in case Map.findWithDefault Flag key modes of
                Flag -> uninterpreted (summaryMeasure Empty key) [child] .== 1 .|| compared
                Sentinel _ _ -> compared

-- | The names that a formula applies to arguments.
appliedIn :: Formula -> Set.Set Formula.Name
appliedIn formula = case formula of
    Formula.And parts -> Set.unions $ map appliedIn parts
    Formula.Or parts -> Set.unions $ map appliedIn parts
    Formula.Not inner -> appliedIn inner
    Formula.Atom _ left right -> appliedInTerm left <> appliedInTerm right
    Formula.Forall _ inner -> appliedIn inner
    Formula.Exists _ inner -> appliedIn inner
    _ -> Set.empty

{- | Turn the Boolean measures that the root requires, and that hold at a
value exactly when a condition holds at each of its nodes, into contracts. The
measure @isRB (Node c x l r) = isRB l && isRB r && local@ holds at the root
exactly when @local@ holds at each node, so @local@ is a conjunct of the
contract of @Node@, and the generator does not build the values where it
fails. A measure that another formula reads stays a measure.
-}
localize ::
    Map.Map TypeRep Datatype ->
    TypeRep ->
    (Formula, [(String, Formula)], Map.Map (TypeRep, String) [(String, Expr)]) ->
    (Formula, [(String, Formula)], Map.Map (TypeRep, String) [(String, Expr)])
localize reached rootRep state@(rootFormula, contracts, measures) =
    case mapMaybe localized candidates of
        (name, locals) : _ ->
            localize
                reached
                rootRep
                ( Formula.conjunction $ filter (/= required name) rootParts
                , [ (constructor, Formula.conjunction [formula, fromMaybe Formula.Top $ lookup constructor locals])
                  | (constructor, formula) <- contracts
                  ]
                , Map.delete (rootRep, name) measures
                )
        [] -> state
  where
    rootParts = parts rootFormula
    parts formula = case formula of
        Formula.And inner -> concatMap parts inner
        Formula.Top -> []
        _ -> [formula]
    holdsAt name term = Formula.Atom Eq (App (fromString name) [term]) (Lit 1)
    required name = holdsAt name (Var $ fromString rootVariable)
    candidates = [name | (owner, name) <- Map.keys measures, owner == rootRep, required name `elem` rootParts]
    localized name = do
        let others =
                [term | ((owner, other), equations) <- Map.toList measures, (owner, other) /= (rootRep, name), (_, term) <- equations]
            uses =
                Set.unions $
                    map (appliedInTerm . fromExpr) others
                        <> map (appliedIn . snd) contracts
                        <> map appliedIn (filter (/= required name) rootParts)
        guard $ not $ Set.member (fromString name) uses
        equations <- Map.lookup (rootRep, name) measures
        locals <- forM (maybe [] datatypeAlternatives $ Map.lookup rootRep reached) $ \(constructor, children) -> do
            term <- lookup (constructorName constructor) equations
            formula <- case fromExpr term of
                Ite condition (Lit 1) (Lit 0) -> Just condition
                Lit 1 -> Just Formula.Top
                _ -> Nothing
            let own position = holdsAt name (Var $ fromString $ contractTermName $ ArgumentIndex position)
                recursive = [own position | (position, AlgebraicType rep _) <- zip [0 ..] children, rep == rootRep]
                local = Formula.conjunction [part | part <- parts formula, part `notElem` recursive]
            guard $ all (`elem` parts formula) recursive
            guard $ not $ Set.member (fromString name) (appliedIn local)
            guard $ not (null children) || local == Formula.Top
            Just (constructorName constructor, local)
        Just (name, locals)

-- | Read each of the named measures of a value as the value itself.
unnameFormula :: Set.Set Formula.Name -> Formula -> Formula
unnameFormula names formula = case formula of
    Formula.And parts -> Formula.And $ map (unnameFormula names) parts
    Formula.Or parts -> Formula.Or $ map (unnameFormula names) parts
    Formula.Not inner -> Formula.Not $ unnameFormula names inner
    Formula.Atom relation left right -> Formula.Atom relation (unnameTerm names left) (unnameTerm names right)
    Formula.Forall bound inner -> Formula.Forall bound $ unnameFormula names inner
    Formula.Exists bound inner -> Formula.Exists bound $ unnameFormula names inner
    _ -> formula

-- | Read each of the named measures of a value in a term as the value itself.
unnameTerm :: Set.Set Formula.Name -> Term -> Term
unnameTerm names term = case term of
    App name [argument] | Set.member name names -> unnameTerm names argument
    App name arguments -> App name $ map (unnameTerm names) arguments
    Neg inner -> Neg $ unnameTerm names inner
    Add left right -> Add (unnameTerm names left) (unnameTerm names right)
    Sub left right -> Sub (unnameTerm names left) (unnameTerm names right)
    Mul left right -> Mul (unnameTerm names left) (unnameTerm names right)
    Div left right -> Div (unnameTerm names left) (unnameTerm names right)
    Mod left right -> Mod (unnameTerm names left) (unnameTerm names right)
    Ite condition yes no -> Ite (unnameFormula names condition) (unnameTerm names yes) (unnameTerm names no)
    _ -> term

-- | The names that a term applies to arguments.
appliedInTerm :: Term -> Set.Set Formula.Name
appliedInTerm term = case term of
    App name arguments -> Set.insert name $ Set.unions $ map appliedInTerm arguments
    Neg inner -> appliedInTerm inner
    Add left right -> appliedInTerm left <> appliedInTerm right
    Sub left right -> appliedInTerm left <> appliedInTerm right
    Mul left right -> appliedInTerm left <> appliedInTerm right
    Div left right -> appliedInTerm left <> appliedInTerm right
    Mod left right -> appliedInTerm left <> appliedInTerm right
    Ite condition yes no -> appliedIn condition <> appliedInTerm yes <> appliedInTerm no
    _ -> Set.empty

{- | The equations of the named measures that the formulas need, by datatype
and name, with one term for each constructor. A measure equation can need
more measures.
-}
neededMeasures ::
    Context ->
    Map.Map SummaryKey Mode ->
    Map.Map TypeRep [(String, Rules)] ->
    Set.Set Formula.Name ->
    Either LiquidError (Map.Map (TypeRep, String) [(String, Expr)])
neededMeasures context modes rules = go Map.empty
  where
    nameText (Formula.Name text) = Text.unpack text
    derived =
        Map.fromList $
            [ (summaryMeasure summary key, (fst key, Left (summary, key)))
            | (key, mode) <- Map.toList modes
            , summary <- [Least, Greatest] <> [Empty | Flag <- [mode]]
            ]
                <> [ (enumerationMeasure rep, (rep, Right Nothing))
                   | (rep, datatype) <- Map.toList (contextTypes context)
                   , isEnumeration datatype
                   ]
                <> [ (name, (rep, Right (Just measure')))
                   | (name, measure') <- Map.toList (indexMeasures $ contextIndex context)
                   , Just input <- [measureInput measure']
                   , Just rep <- [Map.lookup input (contextNames context)]
                   ]
    go done pending = case [name | name <- map nameText (Set.toList pending), Map.member name derived, not (Map.member (owner name, name) done)] of
        [] -> Right done
        names -> do
            generated <- forM names $ \name -> do
                let (rep, kind) = derived Map.! name
                equations <- equationsOf rep name kind
                Right ((rep, name), equations)
            let next = Map.union done (Map.fromList generated)
                more = Set.unions [appliedInTerm (fromExpr term) | (_, equations) <- generated, (_, term) <- equations]
            go next more
    owner name = fst (derived Map.! name)
    equationsOf rep name kind = do
        datatype <-
            maybe (Left $ Untranslatable name "the measure is of a datatype that the target does not reach") Right $
                Map.lookup rep (contextTypes context)
        forM (zip [0 :: Integer ..] (datatypeAlternatives datatype)) $ \(position, (constructor, children)) ->
            (,) (constructorName constructor) <$> case kind of
                Right Nothing -> Right $ fromInteger position
                Right (Just measure') -> measureEquation measure' (constructorName constructor) children
                Left (summary, key) -> do
                    constructorRules' <-
                        maybe (Left $ Untranslatable name "the constructor has no rules") Right $
                            lookup (constructorName constructor) (Map.findWithDefault [] rep rules)
                    summaryEquation (Map.findWithDefault Flag key modes) summary key constructorRules'
    measureEquation measure' name children = do
        let measureName = nameOf $ F.val $ msName measure'
        equation <-
            maybe
                ( Left
                    $ Untranslatable (placeOf (msName measure') ("the measure " <> measureName))
                    $ "the measure has no equation for " <> name
                )
                Right
                $ find ((== name) . nameOf . F.val . ctor) (msEqns measure')
        let place = placeOf (ctor equation) ("the measure " <> measureName <> " of " <> name)
            binders = [symbolName binder | (binder, _) <- binds equation]
        when (length binders /= length children)
            $ Left
            $ Untranslatable place
            $ "the equation binds " <> show (length binders) <> " fields, and the constructor has " <> show (length children)
        sort <- measureSort context measure'
        let environment = Map.fromList $ zip binders (zipWith fieldValue [0 ..] children)
        value <- case body equation of
            E expression -> evaluate context place environment expression
            P expression -> evaluate context place environment expression
            R _ _ -> Left $ Untranslatable place "an equation of the form {v | p} is not translated"
        case (sort, value) of
            (BooleanSort, TruthValue f) -> Right $ booleanTerm f
            (BooleanSort, _) -> Left $ Untranslatable place "the equation of a Boolean measure is not a formula"
            (_, TermValue t) -> Right t
            (EnumerationSort, NodeValue childRep node)
                | Just childType <- Map.lookup childRep (contextTypes context)
                , isEnumeration childType ->
                    Right $ uninterpreted (enumerationMeasure childRep) [node]
            _ -> Left $ Untranslatable place "the equation is not a term"
    booleanTerm f
        | f == Formula.Top = 1
        | f == Formula.Bottom = 0
        | otherwise = toExpr $ Ite f (Lit 1) (Lit 0)
    summaryEquation mode summary key constructorRules' = do
        let (rep, position) = key
        variableName <-
            maybe (Left $ Untranslatable (lhNameOf rep) "the datatype has no type variable for the elements") Right $
                Map.lookup rep (contextTypes context) >>= datatypeDeclaration >>= at position . declarationVariables
        let elements = Map.findWithDefault [] variableName (rulesElements constructorRules')
            carrying =
                [ child
                | (child, childRep, variables) <- rulesChildren constructorRules'
                , childRep == rep
                , at position variables == Just (Just variableName)
                ]
            others =
                [ child
                | (child, _, variables) <- rulesChildren constructorRules'
                , Just variableName `elem` variables
                , child `notElem` carrying
                ]
        unless (null others)
            $ Left
            $ Untranslatable (lhNameOf rep) "the elements of a derived measure are inside a field of another datatype"
        let dominated side' =
                [ boundChild bound
                | bound <- rulesBounds constructorRules'
                , boundKey bound == key
                , boundSide bound `elem` [side', Equal]
                , boundCoefficient bound == 1
                , Just element <- [boundElement bound]
                , element `elem` elements
                ]
            measureOf summary' child = uninterpreted (summaryMeasure summary' key) [fieldTerm child]
            emptyOf child = measureOf Empty child .== 1
            choose better candidates = case mode of
                Sentinel lower upper ->
                    let sentinel = case summary of
                            Least -> maybe 0 (+ 1) upper
                            _ -> maybe 0 (subtract 1) lower
                     in case candidates of
                            [] -> fromInteger sentinel
                            _ -> foldr1 better [term | (_, term) <- candidates]
                Flag ->
                    -- Each partial result has the condition that it has no
                    -- elements; the elements of the node are never empty.
                    let combine (noneSoFar, value) (child, term) =
                            ( Formula.conjunction [emptyOf child, noneSoFar]
                            , choice (emptyOf child) value (choice noneSoFar term (better term value))
                            )
                        children = [(child, term) | (Just child, term) <- candidates]
                     in case ([term | (Nothing, term) <- candidates], children) of
                            ([], []) -> 0
                            ([], (child, term) : rest) -> snd $ foldl combine (emptyOf child, term) rest
                            (terms, _) -> snd $ foldl combine (Formula.Bottom, foldr1 better terms) children
            choice condition yes no
                | condition == Formula.Bottom = no
                | otherwise = toExpr $ Ite condition (fromExpr yes) (fromExpr no)
            least a b = toExpr $ Ite (a .<= b) (fromExpr a) (fromExpr b)
            greatest a b = toExpr $ Ite (a .>= b) (fromExpr a) (fromExpr b)
            candidatesFor summary' side' =
                [(Nothing, fieldTerm element) | element <- elements]
                    <> [(Just child, measureOf summary' child) | child <- carrying, child `notElem` dominated side']
        Right $ case summary of
            Least -> choose least (candidatesFor Least Lower)
            Greatest -> choose greatest (candidatesFor Greatest Upper)
            Empty
                | not (null elements) -> 0
                | null carrying -> 1
                | otherwise -> toExpr $ Ite (Formula.conjunction $ map emptyOf carrying) (Lit 1) (Lit 0)
