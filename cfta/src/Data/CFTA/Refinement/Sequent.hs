{- | Horn clauses and geometric sequents in the formula language.

A geometric sequent is a formula of the form

@forall x1 ... xn. a1 and ... and ak  ==>  (exists y1. b1) or ... or (exists ym. bm)@

where each @ai@ is an atom, and each @bi@ is a conjunction of atoms. An atom
is a comparison ('Atom') or the application of a predicate ('Predicate'). A
Horn clause is a geometric sequent with at most one disjunct in its head, and
that disjunct is one atom without an existential quantifier. A sequent with
no disjunct in its head is a goal: its body cannot hold.

The formula language has no implication, so @a ==> b@ is written
@not a or b@. 'sequent' reads a formula in that form, and also in forms that
are equivalent to it, and gives the sequent:

* nested universal quantifiers at the top, which it joins;
* a disjunction of negated parts (the body) and other parts (the head), in
  any order and with nested disjunctions;
* a negated conjunction of atoms as a part of the body;
* a double negation, which is the part without the negations;
* nested existential quantifiers in a part of the head, which it joins;
* a universal quantifier as a part of the head, and an existential
  quantifier under a negation in the body, which it moves to the top when
  its bound names occur nowhere else in the formula.

A formula that has no such form gives the part where it leaves the form.
-}
module Data.CFTA.Refinement.Sequent (
    Sequent (..),
    Shape (..),
    Place (..),
    NotGeometric (..),
    sequent,
    shape,
    sequentFormula,
) where

import Control.Monad (foldM)
import Data.List (find)

import Data.CFTA.Formula (Formula (..), Name, Sort, freeNames)

-- | A geometric sequent.
data Sequent = Sequent
    { sequentBound :: ![(Name, Sort)]
    -- ^ The names that the sequent binds for all values.
    , sequentBody :: ![Formula]
    -- ^ The atoms of the body.
    , sequentHead :: ![([(Name, Sort)], [Formula])]
    -- ^ The disjuncts of the head: the existentially bound names and the atoms of each.
    }
    deriving (Eq, Show)

-- | The form of a sequent.
data Shape
    = -- | At most one atom in the head, without an existential quantifier.
      Horn
    | -- | A sequent that is not a Horn clause.
      Geometric
    deriving (Eq, Show)

-- | Where a formula leaves the form of a sequent.
data Place = InBody | InHead
    deriving (Eq, Show)

-- | Why a formula is not a geometric sequent.
data NotGeometric
    = -- | A part that must be an atom or a conjunction of atoms, and is not.
      NotAtomic !Place !Formula
    | -- | A quantifier would move to the top, but its bound name occurs elsewhere in the formula.
      Captures !Name
    deriving (Eq, Show)

-- | The geometric sequent of a formula, or the part where the formula leaves that form.
sequent :: Formula -> Either NotGeometric Sequent
sequent original = do
    let (bound, matrix) = universals original
    (lifted, body, heads) <- foldM part ([], [], []) (disjuncts matrix)
    pure $ Sequent (bound <> lifted) body heads
  where
    universals (Forall binders inner) = let (more, matrix) = universals inner in (binders <> more, matrix)
    universals matrix = ([], matrix)
    disjuncts (Or parts) = concatMap disjuncts parts
    disjuncts Bottom = []
    disjuncts other = [other]
    part (lifted, body, heads) current = case current of
        Not (Not inner) -> foldM part (lifted, body, heads) (disjuncts inner)
        Not (Exists binders inner) -> do
            free lifted binders current
            atoms <- conjunction InBody inner
            pure (lifted <> binders, body <> atoms, heads)
        Not inner -> do
            atoms <- conjunction InBody inner
            pure (lifted, body <> atoms, heads)
        Forall binders inner -> do
            free lifted binders current
            foldM part (lifted <> binders, body, heads) (disjuncts inner)
        _ -> do
            disjunct <- headDisjunct current
            pure (lifted, body, heads <> [disjunct])
    headDisjunct (Exists binders inner) = do
        (more, atoms) <- headDisjunct inner
        pure (binders <> more, atoms)
    headDisjunct inner = (,) [] <$> conjunction InHead inner
    conjunction place current = case current of
        And parts -> concat <$> traverse (conjunction place) parts
        Top -> Right []
        Atom{} -> Right [current]
        Predicate{} -> Right [current]
        _ -> Left $ NotAtomic place current
    {- A quantifier of a part moves to the top only when its names are not
    bound at the top, not moved there before, and not free in another part. -}
    free lifted binders current =
        case find (`elem` outside) (map fst binders) of
            Just name -> Left $ Captures name
            Nothing -> Right ()
      where
        outside =
            map fst lifted
                <> map fst (fst $ universals original)
                <> concatMap freeNames (filter (/= current) $ disjuncts $ snd $ universals original)

-- | The form of a sequent.
shape :: Sequent -> Shape
shape current = case sequentHead current of
    [] -> Horn
    [([], [_])] -> Horn
    _ -> Geometric

-- | The formula of a sequent: the universal quantifier of the bound names over a negated body or a head.
sequentFormula :: Sequent -> Formula
sequentFormula (Sequent bound body heads) =
    quantified Forall bound
        $ Or
        $ [Not (And body) | not (null body)]
            <> [quantified Exists binders (And atoms) | (binders, atoms) <- heads]
  where
    quantified _ [] inner = inner
    quantified quantifier binders inner = quantifier binders inner
