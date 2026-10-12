{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

{- | The formulas of the refinement logic.

A 'Formula' states a fact about named values. A 'Term' gives a value from
names, literals, arithmetic, and applications of uninterpreted functions. An
atom compares two terms, the connectives combine formulas, and a quantifier
binds names of a 'Sort'. 'substitute' renames a bound name that a
replacement would capture.

The liquid tree automata build only integer terms without quantifiers.
'Data.CFTA.Refinement.Lattice' decides only those. The Z3 entailment
translates every form.

'conjunction' and 'disjunction' simplify their result as the functions
@pAnd@ and @pOr@ of Liquid Fixpoint do. Formula equality decides the interning
of symbols and the hits of solver caches, so the simplification must not
change.

The constructor order of each type is the order of the matching constructors
of Liquid Fixpoint. The derived 'Ord' instances therefore order formulas as
Liquid Fixpoint does. 'conjunction' sorts its parts by this order, and symbols
with the same text sort by it.
-}
module Data.CFTA.Formula (
    Name (..),
    Term (..),
    Relation (..),
    Formula (..),
    Sort (..),
    conjunction,
    disjunction,
    implies,
    iff,
    freeNames,
    substitute,
    substituteChecked,
    SubstitutionError (..),
    renderFormula,
    renderTerm,
) where

import Data.Functor.Identity (Identity (..))
import qualified Data.HashSet as HashSet
import Data.Hashable (Hashable (..))
import Data.List (intercalate, nub)
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import Data.String (IsString (..))
import Data.Text (Text)
import qualified Data.Text as Text
import GHC.Generics (Generic)

-- | The name of a value or of a function. It shows as its text.
newtype Name = Name Text
    deriving newtype (Eq, Ord, Show)

{- | A name hashes as its text. The instance defines only 'hashWithSalt', so
'hash' uses the default salt, as for the symbols of Liquid Fixpoint. A hash set
of names then lists them in the order of Liquid Fixpoint, and 'freeNames'
keeps that order.
-}
instance Hashable Name where
    hashWithSalt salt (Name text) = hashWithSalt salt text

instance IsString Name where
    fromString = Name . Text.pack

-- | A term: a value of the logic.
data Term
    = -- | An integer literal.
      Lit !Integer
    | -- | A named value.
      Var !Name
    | -- | An uninterpreted function applied to its arguments.
      App !Name ![Term]
    | -- | The negation of a term.
      Neg !Term
    | -- | The sum of two terms.
      Add !Term !Term
    | -- | The difference of two terms.
      Sub !Term !Term
    | -- | The product of two terms.
      Mul !Term !Term
    | -- | The integer quotient of two terms.
      Div !Term !Term
    | -- | The remainder of the integer division of two terms.
      Mod !Term !Term
    | -- | The first term when the formula holds, and the second term when it does not.
      Ite !Formula !Term !Term
    | -- | A term with a given sort.
      Cast !Term !Sort
    deriving (Eq, Ord, Show, Generic)

instance Hashable Term

-- | A comparison of two terms.
data Relation = Eq | Ne | Gt | Ge | Lt | Le
    deriving (Eq, Ord, Show, Enum, Generic)

instance Hashable Relation

{- | A formula. 'Top' is the empty conjunction and 'Bottom' is the empty
disjunction: 'conjunction' and 'disjunction' do not give an 'And' or an 'Or'
without parts.
-}
data Formula
    = -- | The formula that always holds.
      Top
    | -- | All parts hold.
      And ![Formula]
    | -- | The formula that never holds.
      Bottom
    | -- | At least one part holds.
      Or ![Formula]
    | -- | The formula does not hold.
      Not !Formula
    | -- | The relation holds between the two terms.
      Atom !Relation !Term !Term
    | -- | The formula holds for all values of the bound names.
      Forall ![(Name, Sort)] !Formula
    | -- | The formula holds for some values of the bound names.
      Exists ![(Name, Sort)] !Formula
    deriving (Eq, Ord, Show, Generic)

instance Hashable Formula

-- | The sort of a name: integers, reals, booleans, or a function.
data Sort
    = IntSort
    | RealSort
    | BoolSort
    | -- | A function from the argument sorts to the result sort.
      FunctionSort ![Sort] !Sort
    deriving (Eq, Ord, Show, Generic)

instance Hashable Sort

{- | The conjunction of the formulas, simplified as @pAnd@ of Liquid Fixpoint.

A contradiction among the formulas gives 'Bottom'. Otherwise each formula is
simplified, and tautologies go. Nested conjunctions are flattened, and the
parts are sorted without duplicates. No part gives 'Top', and one part gives
that part.
-}
conjunction :: [Formula] -> Formula
conjunction = simplify . And

{- | The disjunction of the formulas, simplified as @pOr@ of Liquid Fixpoint.

A tautology among the formulas gives 'Top'. Otherwise each formula is
simplified, and contradictions go. The parts are not flattened, sorted, or
made distinct. One formula gives that formula, simplified. No remaining part
gives 'Bottom', and one remaining part gives an 'Or' of that part.
-}
disjunction :: [Formula] -> Formula
disjunction = simplify . Or

{- | Simplify a formula as @simplify@ of Liquid Fixpoint does.

Only a conjunction, a disjunction, or a negation changes below the root. A
negation of a negation becomes the inner formula. An atom that is a tautology
or a contradiction becomes 'Top' or 'Bottom'.
-}
simplify :: Formula -> Formula
simplify formula = case formula of
    Or [] -> Bottom
    Or [part] -> simplify part
    Not inner -> case simplify inner of
        Not negated -> negated
        simplified -> Not simplified
    And parts
        | any contradiction parts -> Bottom
        | otherwise -> case Set.toList $ Set.fromList $ flatten $ filter (not . tautology) $ map simplify parts of
            [] -> Top
            [part] -> part
            several -> And several
    Or parts
        | any tautology parts -> Top
        | otherwise -> case filter (not . contradiction) $ map simplify parts of
            [] -> Bottom
            kept -> Or kept
    _
        | contradiction formula -> Bottom
        | tautology formula -> Top
        | otherwise -> formula
  where
    flatten = concatMap $ \part -> case part of
        And nested -> flatten nested
        _ -> [part]

-- | Whether a formula is 'Top' or an atom that always holds.
tautology :: Formula -> Bool
tautology formula = case formula of
    Top -> True
    Atom Eq left right -> left == right
    Atom Le left right -> left == right
    Atom Ge left right -> left == right
    Atom Ne (Lit left) (Lit right) -> left /= right
    _ -> False

-- | Whether a formula is 'Bottom' or an atom that never holds.
contradiction :: Formula -> Bool
contradiction formula = case formula of
    Bottom -> True
    Atom Eq (Lit left) (Lit right) -> left /= right
    Atom Ne left right -> left == right
    _ -> False

-- | The first formula implies the second. The result is not simplified.
implies :: Formula -> Formula -> Formula
implies premise conclusion = Or [Not premise, conclusion]

-- | Both formulas hold or neither holds. The result is not simplified.
iff :: Formula -> Formula -> Formula
iff left right = Or [And [left, right], And [Not left, Not right]]

{- | The free names in a formula, each once: the names of values and of
applied functions, without the names that a quantifier binds.

The order is the order of a hash set of the names, as for @syms@ of Liquid
Fixpoint. It is the same in each process.
-}
freeNames :: Formula -> [Name]
freeNames = HashSet.toList . namesIn

-- | The free names of a formula as a set.
namesIn :: Formula -> HashSet.HashSet Name
namesIn formula = case formula of
    Top -> HashSet.empty
    And parts -> foldMap namesIn parts
    Bottom -> HashSet.empty
    Or parts -> foldMap namesIn parts
    Not inner -> namesIn inner
    Atom _ left right -> termNames left <> termNames right
    Forall bound inner -> HashSet.difference (namesIn inner) (HashSet.fromList $ map fst bound)
    Exists bound inner -> HashSet.difference (namesIn inner) (HashSet.fromList $ map fst bound)

-- | The free names of a term as a set.
termNames :: Term -> HashSet.HashSet Name
termNames term = case term of
    Lit _ -> HashSet.empty
    Var name -> HashSet.singleton name
    App function arguments -> HashSet.insert function $ foldMap termNames arguments
    Neg inner -> termNames inner
    Add left right -> termNames left <> termNames right
    Sub left right -> termNames left <> termNames right
    Mul left right -> termNames left <> termNames right
    Div left right -> termNames left <> termNames right
    Mod left right -> termNames left <> termNames right
    Ite condition yes no -> namesIn condition <> termNames yes <> termNames no
    Cast inner _ -> termNames inner

-- | A replacement that cannot be applied to the named-function syntax.
data SubstitutionError = UnsupportedFunctionReplacement !Name !Term
    deriving (Eq, Ord, Show)

{- | Replace names by terms, all at once.

For a name with more than one replacement, the first replacement applies. A
replacement of a name by the same name is ignored, and so is a replacement of
a name that a quantifier binds. A bound name that occurs in a replacement
gets a fresh name, so that the replacement is not captured. A nullary
application is a named value. A non-nullary function name can be replaced
only by a 'Var', because 'App' requires a name as its head. A replacement of
a function name by another term leaves the applications of that name as they
are; use 'substituteChecked' to find such a replacement. The result is not
simplified.
-}
substitute :: [(Name, Term)] -> Formula -> Formula
substitute replacements = runIdentity . substituteWith (\function _ arguments -> Identity (App function arguments)) replacements

-- | Substitute simultaneously, or report an unsupported function replacement.
substituteChecked :: [(Name, Term)] -> Formula -> Either SubstitutionError Formula
substituteChecked = substituteWith (\function replacement _ -> Left (UnsupportedFunctionReplacement function replacement))

{- | Substitute simultaneously. The function decides an application whose
function name has a replacement that is not a name; it gets the name, the
replacement, and the substituted arguments.
-}
substituteWith ::
    (Monad effect) =>
    (Name -> Term -> [Term] -> effect Term) ->
    [(Name, Term)] ->
    Formula ->
    effect Formula
substituteWith unsupported replacements = inFormula (filter (\(name, term) -> term /= Var name) replacements)
  where
    inFormula active formula = case formula of
        And parts -> And <$> traverse (inFormula active) parts
        Or parts -> Or <$> traverse (inFormula active) parts
        Not inner -> Not <$> inFormula active inner
        Atom relation left right -> Atom relation <$> inTerm active left <*> inTerm active right
        Forall bound inner -> uncurry Forall <$> underBinders active bound inner
        Exists bound inner -> uncurry Exists <$> underBinders active bound inner
        _ -> pure formula
    inTerm active term = case term of
        Var name -> pure $ fromMaybe term $ lookup name active
        App function [] -> pure $ fromMaybe term $ lookup function active
        App function arguments -> case lookup function active of
            Nothing -> App function <$> traverse (inTerm active) arguments
            Just (Var renamed) -> App renamed <$> traverse (inTerm active) arguments
            Just replacement -> unsupported function replacement =<< traverse (inTerm active) arguments
        Neg inner -> Neg <$> inTerm active inner
        Add left right -> Add <$> inTerm active left <*> inTerm active right
        Sub left right -> Sub <$> inTerm active left <*> inTerm active right
        Mul left right -> Mul <$> inTerm active left <*> inTerm active right
        Div left right -> Div <$> inTerm active left <*> inTerm active right
        Mod left right -> Mod <$> inTerm active left <*> inTerm active right
        Ite condition yes no -> Ite <$> inFormula active condition <*> inTerm active yes <*> inTerm active no
        Cast inner sort -> (`Cast` sort) <$> inTerm active inner
        Lit _ -> pure term
    -- The replacements of the bound names stop, and a bound name that a
    -- replacement mentions becomes the first fresh name.
    underBinders active bound inner =
        let kept = [(name, term) | (name, term) <- active, name `notElem` map fst bound]
            captured = foldMap (termNames . snd) kept
            avoid = captured <> namesIn inner <> HashSet.fromList (map fst bound <> map fst kept)
            -- Repeated binders keep one name, so the last binder still shadows
            -- the earlier binders of that name.
            renamed = zip (filter (`HashSet.member` captured) $ nub $ map fst bound) (freshNames avoid)
            bindings = [(fromMaybe name $ lookup name renamed, sort) | (name, sort) <- bound]
            active' = [(name, Var fresh) | (name, fresh) <- renamed] <> kept
         in (,) bindings <$> inFormula active' inner
    freshNames avoid =
        [ candidate
        | index <- [1 :: Integer ..]
        , let candidate = Name $ Text.pack $ "__microcfta_bound_" <> show index
        , not $ HashSet.member candidate avoid
        ]

{- | A formula as text, in the notation of the operators of
"Data.CFTA.Refinement.Expression", as in @__microcfta_value >= 0 && x /= y@. A
conjunction or a disjunction inside another formula gets parentheses, and so
does an atom inside a negation.
-}
renderFormula :: Formula -> String
renderFormula = go (0 :: Int)
  where
    go context formula = case formula of
        Top -> "true"
        Bottom -> "false"
        Atom relation left right ->
            parenthesize (context >= 2) $ renderTerm left <> " " <> operator relation <> " " <> renderTerm right
        Not inner -> "not " <> go 2 inner
        And [] -> "true"
        And parts -> parenthesize (context >= 1) $ intercalate " && " $ map (go 1) parts
        Or [] -> "false"
        Or parts -> parenthesize (context >= 1) $ intercalate " || " $ map (go 1) parts
        Forall bound inner -> parenthesize (context >= 1) $ "forall " <> binders bound <> ". " <> go 0 inner
        Exists bound inner -> parenthesize (context >= 1) $ "exists " <> binders bound <> ". " <> go 0 inner
    binders bound = unwords ["(" <> Text.unpack name <> " : " <> renderSort sort <> ")" | (Name name, sort) <- bound]
    operator relation = case relation of
        Eq -> "=="
        Ne -> "/="
        Gt -> ">"
        Ge -> ">="
        Lt -> "<"
        Le -> "<="

{- | A term as text: names, literals, @+@, @-@, @*@, @div@, @mod@, function
applications as @f(x, y)@, @if then else@, and casts as @(x : Int)@, with the
parentheses that the precedence of the operators needs.
-}
renderTerm :: Term -> String
renderTerm = go (0 :: Int)
  where
    go context term = case term of
        Lit value -> parenthesize (value < 0 && context > 0) $ show value
        Var (Name name) -> Text.unpack name
        Neg inner -> parenthesize (context > 6) $ "-" <> go 9 inner
        Add left right -> parenthesize (context > 6) $ go 6 left <> " + " <> go 7 right
        Sub left right -> parenthesize (context > 6) $ go 6 left <> " - " <> go 7 right
        Mul left right -> parenthesize (context > 7) $ go 7 left <> " * " <> go 8 right
        Div left right -> parenthesize (context > 7) $ go 7 left <> " `div` " <> go 8 right
        Mod left right -> parenthesize (context > 7) $ go 7 left <> " `mod` " <> go 8 right
        App (Name function) arguments -> Text.unpack function <> "(" <> intercalate ", " (map (go 0) arguments) <> ")"
        Cast inner sort -> "(" <> go 0 inner <> " : " <> renderSort sort <> ")"
        Ite condition yes no ->
            parenthesize (context > 0) $ "if " <> renderFormula condition <> " then " <> go 0 yes <> " else " <> go 0 no

-- | A sort as text, as in @Int -> Bool@.
renderSort :: Sort -> String
renderSort sort = case sort of
    IntSort -> "Int"
    RealSort -> "Real"
    BoolSort -> "Bool"
    FunctionSort arguments result -> intercalate " -> " $ map argument arguments <> [renderSort result]
  where
    argument function@FunctionSort{} = "(" <> renderSort function <> ")"
    argument other = renderSort other

-- | The text in parentheses when the condition holds.
parenthesize :: Bool -> String -> String
parenthesize True text = "(" <> text <> ")"
parenthesize False text = text
