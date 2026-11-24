{-# LANGUAGE OverloadedStrings #-}

{- | Horn clauses and geometric sequents in the formula language: the forms
that 'sequent' reads, the reasons why it refuses a formula, the shape of a
sequent, and the formula of a sequent.
-}
module Data.CFTA.Refinement.SequentSpec (spec) where

import Control.Monad (forM_)
import Test.Hspec (Spec, describe, it, shouldBe)

import Data.CFTA.Formula (Formula (..), Name, Relation (..), Sort (..), Term (..))
import Data.CFTA.Refinement.Sequent

-- | Names of the sort Int.
ints :: [Name] -> [(Name, Sort)]
ints names = [(name, IntSort) | name <- names]

-- | The predicates of a graph with two arguments.
edge, path :: Term -> Term -> Formula
edge from to = Predicate "edge" [from, to]
path from to = Predicate "path" [from, to]

-- | The predicates of a graph with one argument.
node, red, blue :: Term -> Formula
node at = Predicate "node" [at]
red at = Predicate "red" [at]
blue at = Predicate "blue" [at]

x, y, z :: Term
x = Var "x"
y = Var "y"
z = Var "z"

-- | Each form of the module comment: a description, a formula, and its sequent.
forms :: [(String, Formula, Sequent)]
forms =
    [ ("an atom, which is a fact", edge (Lit 1) (Lit 2), Sequent [] [] [([], [edge (Lit 1) (Lit 2)])])
    , ("a negated atom, which is a goal", Forall (ints ["x"]) (Not (path x x)), Sequent (ints ["x"]) [path x x] [])
    ,
        ( "nested universal quantifiers at the top"
        , Forall (ints ["x"]) (Forall (ints ["y", "z"]) (Or [Not (And [path x y, edge y z]), path x z]))
        , Sequent (ints ["x", "y", "z"]) [path x y, edge y z] [([], [path x z])]
        )
    ,
        ( "a head part before a body part, in nested disjunctions"
        , Forall (ints ["x"]) (Or [red x, Or [Not (node x), blue x]])
        , Sequent (ints ["x"]) [node x] [([], [red x]), ([], [blue x])]
        )
    ,
        ( "a negated conjunction and a negated atom in the body"
        , Forall (ints ["x", "y"]) (Or [Not (And [node x, node y]), Not (edge x y), path x y])
        , Sequent (ints ["x", "y"]) [node x, node y, edge x y] [([], [path x y])]
        )
    ,
        ( "a double negation of a part"
        , Forall (ints ["x"]) (Or [node x, Not (Not (Not (edge x x)))])
        , Sequent (ints ["x"]) [edge x x] [([], [node x])]
        )
    ,
        ( "a double negation of a disjunction"
        , Not (Not (Or [Not (node (Lit 0)), red (Lit 0)]))
        , Sequent [] [node (Lit 0)] [([], [red (Lit 0)])]
        )
    ,
        ( "nested existential quantifiers in the head"
        , Forall (ints ["x"]) (Or [Not (node x), Exists (ints ["y"]) (Exists (ints ["z"]) (And [edge x y, edge y z]))])
        , Sequent (ints ["x"]) [node x] [(ints ["y", "z"], [edge x y, edge y z])]
        )
    ,
        ( "a universal quantifier as a part of the head"
        , Forall (ints ["x"]) (Or [Not (node x), Forall (ints ["y"]) (edge x y)])
        , Sequent (ints ["x", "y"]) [node x] [([], [edge x y])]
        )
    ,
        ( "an existential quantifier under a negation in the body"
        , Forall (ints ["x"]) (Or [Not (Exists (ints ["y"]) (edge x y)), node x])
        , Sequent (ints ["x", "y"]) [edge x y] [([], [node x])]
        )
    ,
        ( "the empty conjunction in the body and the empty disjunction"
        , Forall (ints ["x"]) (Or [Not (And [node x, Top]), Bottom])
        , Sequent (ints ["x"]) [node x] []
        )
    ,
        ( "comparisons"
        , Forall (ints ["x", "y"]) (Or [Not (Atom Lt x y), Atom Le x y])
        , Sequent (ints ["x", "y"]) [Atom Lt x y] [([], [Atom Le x y])]
        )
    ]

spec :: Spec
spec = describe "Data.CFTA.Refinement.Sequent" $ do
    describe "sequent" $ do
        forM_ forms $ \(form, formula, expected) ->
            it ("reads " <> form) $ sequent formula `shouldBe` Right expected

        it "gives the part of the body or the head that is not an atom or a conjunction of atoms" $ do
            sequent (Forall (ints ["x"]) (Exists (ints ["y"]) (Not (edge x y))))
                `shouldBe` Left (NotAtomic InHead (Not (edge x y)))
            sequent (And [node (Lit 0), Or [red (Lit 0), blue (Lit 0)]])
                `shouldBe` Left (NotAtomic InHead (Or [red (Lit 0), blue (Lit 0)]))
            sequent (Forall (ints ["x"]) (Or [Not (Or [node x, edge x x]), node x]))
                `shouldBe` Left (NotAtomic InBody (Or [node x, edge x x]))
            sequent (Or [Not (Forall (ints ["y"]) (node y)), edge (Lit 1) (Lit 1)])
                `shouldBe` Left (NotAtomic InBody (Forall (ints ["y"]) (node y)))

        it "gives the name that a quantifier would capture when it moves to the top" $ do
            -- The name is free in another part.
            sequent (Forall (ints ["x"]) (Or [Not (Exists (ints ["y"]) (edge x y)), node y]))
                `shouldBe` Left (Captures "y")
            -- The name is bound at the top.
            sequent (Forall (ints ["y"]) (Or [Not (node y), Forall (ints ["y"]) (edge y y)]))
                `shouldBe` Left (Captures "y")
            -- An earlier part moved the name to the top.
            sequent (Or [Forall (ints ["y"]) (node y), Forall (ints ["y"]) (edge y y)])
                `shouldBe` Left (Captures "y")

    describe "shape" $ do
        it "gives Horn for a head with at most one atom and no existential quantifier" $ do
            shape (Sequent (ints ["x"]) [path x x] []) `shouldBe` Horn
            shape (Sequent [] [] [([], [edge (Lit 1) (Lit 2)])]) `shouldBe` Horn
            shape (Sequent (ints ["x", "y"]) [path x y] [([], [path y x])]) `shouldBe` Horn

        it "gives Geometric for an existential quantifier, two atoms, or two disjuncts in the head" $ do
            shape (Sequent (ints ["x"]) [node x] [(ints ["y"], [edge x y])]) `shouldBe` Geometric
            shape (Sequent (ints ["x"]) [node x] [([], [red x, blue x])]) `shouldBe` Geometric
            shape (Sequent (ints ["x"]) [node x] [([], [red x]), ([], [blue x])]) `shouldBe` Geometric

    describe "sequentFormula" $ do
        it "writes the universal quantifier of the bound names over a negated body or a head" $ do
            sequentFormula (Sequent [] [] []) `shouldBe` Or []
            sequentFormula (Sequent (ints ["x"]) [node x] [([], [red x]), (ints ["y"], [edge x y])])
                `shouldBe` Forall (ints ["x"]) (Or [Not (And [node x]), And [red x], Exists (ints ["y"]) (And [edge x y])])

        it "gives a formula that sequent reads as the same sequent" $
            forM_ forms $
                \(_, _, expected) -> sequent (sequentFormula expected) `shouldBe` Right expected
