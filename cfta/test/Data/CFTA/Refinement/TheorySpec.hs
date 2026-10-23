{-# LANGUAGE OverloadedStrings #-}

-- | The checks of a theory, ground evaluation from a theory, and the predicate definitions of a theory.
module Data.CFTA.Refinement.TheorySpec (spec) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.String (fromString)
import Test.Hspec

import Data.CFTA.Formula (Formula (..), Name, Relation (..), Sort (..), Term (..))
import Data.CFTA.Refinement (Entailment (entails), Verdict (..))
import Data.CFTA.Refinement.Definition (Definition (..), DefinitionError (..))
import Data.CFTA.Refinement.Ground (groundEntailment)
import Data.CFTA.Refinement.LiquidFixpoint (withZ3Definitions)
import Data.CFTA.Refinement.Theory
import Data.CFTA.Symbol (valueName)

-- | The sort of integer lists.
list :: Sort
list = NamedSort "List" [IntSort]

-- | Integer lists.
lists :: Datatype
lists = Datatype list [Constructor "nil" [], Constructor "cons" [("head", IntSort), ("tail", list)]]

-- | A datatype without a value: each constructor needs another stream.
streams :: Datatype
streams = Datatype (NamedSort "Stream" []) [Constructor "next" [("first", IntSort), ("rest", NamedSort "Stream" [])]]

-- | Split a list: the body for the empty list, then the body for a head @h@ and a tail @t@.
onList :: Name -> Body a -> Body a -> Body a
onList scrutinee empty nonEmpty = Split scrutinee [Branch "nil" [] empty, Branch "cons" ["h", "t"] nonEmpty]

-- | Append two lists, by recursion on the first.
append :: (Name, TheoryDefinition)
append =
    ( "append"
    , FunctionDefinition [("xs", list), ("ys", list)] list $
        onList "xs" (Expression (Var "ys")) (Expression (App "cons" [Var "h", App "append" [Var "t", Var "ys"]]))
    )

-- | @x@ is between @lo@ and @hi@.
between :: (Name, TheoryDefinition)
between =
    ( "between"
    , PredicateDefinition
        [("x", IntSort), ("lo", IntSort), ("hi", IntSort)]
        (Expression (And [Atom Le (Var "lo") (Var "x"), Atom Le (Var "x") (Var "hi")]))
    )

-- | A function definition with one parameter.
function :: Name -> (Name, Sort) -> Sort -> Body Term -> (Name, TheoryDefinition)
function name parameter result body = (name, FunctionDefinition [parameter] result body)

-- | A predicate definition with one parameter.
predicate :: Name -> (Name, Sort) -> Body Formula -> (Name, TheoryDefinition)
predicate name parameter body = (name, PredicateDefinition [parameter] body)

-- | The term of a list.
listTerm :: [Integer] -> Term
listTerm = foldr (\x rest -> App "cons" [Lit x, rest]) (App "nil" [])

-- | The value name of a refinement.
value :: Name
value = fromString valueName

spec :: Spec
spec = do
    describe "theory" $ do
        it "accepts recursion on a field of a nested split" $ do
            let alternate =
                    function "alternate" ("xs", list) list
                        $ onList "xs" (Expression (Var "xs"))
                        $ Split
                            "t"
                            [ Branch "nil" [] (Expression (Var "xs"))
                            , Branch "cons" ["g", "u"] (Expression (App "cons" [Var "h", App "alternate" [Var "u"]]))
                            ]
            fmap theoryDefinitions (theory [lists] [alternate]) `shouldBe` Right [alternate]

        it "rejects a datatype for a sort that is not named" $
            theory [Datatype IntSort [Constructor "zero" []]] [] `shouldBe` Left (NotNamedSort IntSort)

        it "rejects two datatypes for one sort" $
            theory [lists, lists] [] `shouldBe` Left (DuplicateDatatype list)

        it "rejects a definition with the name of a constructor" $
            theory [lists] [function "nil" ("xs", list) list (Expression (Var "xs"))] `shouldBe` Left (DuplicateName "nil")

        it "rejects two fields with one name" $
            theory [Datatype (NamedSort "Pair" []) [Constructor "pair" [("x", IntSort), ("x", IntSort)]]] []
                `shouldBe` Left (DuplicateField "pair" "x")

        it "rejects a sort that is not an integer or a datatype" $
            theory [] [predicate "flag" ("b", BoolSort) (Expression Top)] `shouldBe` Left (UnsupportedSort "flag" BoolSort)

        it "rejects a parameter that hides another one" $
            theory [] [("twice", PredicateDefinition [("x", IntSort), ("x", IntSort)] (Expression Top))]
                `shouldBe` Left (HiddenName "twice" "x")

        it "rejects a quantifier that hides a field" $
            theory
                [lists]
                [ predicate "all" ("xs", list) $
                    onList "xs" (Expression Top) (Expression (Forall [("t", list)] (Predicate "all" [Var "t"])))
                ]
                `shouldBe` Left (HiddenName "all" "t")

        it "rejects a body with a free name" $
            theory [] [function "leak" ("x", IntSort) IntSort (Expression (Var "n"))] `shouldBe` Left (UnboundName "leak" "n")

        it "rejects a body whose parts have the wrong sorts" $
            theory [lists] [predicate "negative" ("xs", list) (Expression (Atom Lt (Var "xs") (Lit 0)))]
                `shouldBe` Left (IllSortedBody "negative" (IllSortedAtom Lt (Var "xs") (Lit 0)))

        it "rejects a function body with another sort than the result" $
            theory [lists] [function "size" ("xs", list) IntSort (Expression (Var "xs"))]
                `shouldBe` Left (ResultSort "size" IntSort list)

        it "rejects a split on an integer" $
            theory [] [function "pred" ("n", IntSort) IntSort (Split "n" [])] `shouldBe` Left (NotSplittable "pred" "n")

        it "rejects a split without a branch for each constructor" $
            theory [lists] [function "first" ("xs", list) IntSort (Split "xs" [Branch "cons" ["h", "t"] (Expression (Var "h"))])]
                `shouldBe` Left (BadBranches "first" "xs")

        it "rejects a call of a later definition, and thus two definitions that call each other" $ do
            let parity name other result = predicate name ("xs", list) $ onList "xs" (Expression result) (Expression (Predicate other [Var "t"]))
            theory [lists] [parity "even" "odd" Top, parity "odd" "even" Bottom] `shouldBe` Left (ForwardCall "even" "odd")

        it "rejects a recursive call that does not get a field of a split" $
            theory
                [lists]
                [ function "copy" ("xs", list) list $
                    onList "xs" (Expression (Var "xs")) (Expression (App "copy" [App "cons" [Var "h", Var "t"]]))
                ]
                `shouldBe` Left (NotStructural "copy")

        it "rejects recursion that decreases a different parameter in each call" $ do
            let smaller = Ite (Atom Le (Var "h") (Var "g")) (App "merge" [Var "t", Var "ys"]) (App "merge" [Var "xs", Var "u"])
                merge =
                    FunctionDefinition [("xs", list), ("ys", list)] list
                        $ onList "xs" (Expression (Var "ys"))
                        $ Split "ys" [Branch "nil" [] (Expression (Var "xs")), Branch "cons" ["g", "u"] (Expression smaller)]
            theory [lists] [("merge", merge)] `shouldBe` Left (NotStructural "merge")

    describe "theoryInterpretations" $ do
        let lowered = unsafeTheory [lists, streams] [append]
            ground declarations = groundEntailment (theoryInterpretations lowered) Map.empty (theoryDeclarations lowered <> declarations) []
            computed = Atom Eq (Var value) (App "append" [listTerm [2], listTerm [1]])

        it "evaluates a recursive function" $ do
            entails (ground [(value, list)]) computed (Atom Eq (Var value) (listTerm [2, 1])) >>= (`shouldBe` Yes)
            entails (ground [(value, list)]) computed (Atom Eq (Var value) (listTerm [1, 2])) >>= (`shouldBe` No)

        it "finds the datatypes with a value" $
            inhabitedDatatypes lowered `shouldBe` Set.fromList [list]

        it "gives Unknown in place of No when a declared value has a datatype without values" $
            entails (ground [(value, list), ("s", NamedSort "Stream" [])]) computed (Atom Eq (Var value) (listTerm [1, 2]))
                >>= (`shouldBe` Unknown)

    describe "predicateDefinitions" $ do
        let digit = predicate "digit" ("d", IntSort) (Expression (Predicate "between" [Var "d", Lit 0, Lit 9]))
            double = function "double" ("n", IntSort) IntSort (Expression (Add (Var "n") (Var "n")))
            small = predicate "small" ("n", IntSort) (Expression (Predicate "digit" [App "double" [Var "n"]]))
            empty = predicate "empty" ("xs", list) (onList "xs" (Expression Top) (Expression Bottom))
            integers = unsafeTheory [lists] [between, digit, double, small, empty]

        it "gives the predicates that unfold without the names of the theory" $
            predicateDefinitions integers
                `shouldBe` Map.fromList
                    [(name, Definition parameters body) | (name, PredicateDefinition parameters (Expression body)) <- [between, digit]]

        it "lets Z3 unfold them" $
            withZ3Definitions (predicateDefinitions integers) [(value, IntSort)] [] $ \z3 -> do
                entails z3 (Atom Eq (Var value) (Lit 7)) (Predicate "digit" [Var value]) >>= (`shouldBe` Yes)
                entails z3 (Atom Eq (Var value) (Lit 12)) (Predicate "digit" [Var value]) >>= (`shouldBe` No)

-- | A theory that the test expects 'theory' to accept.
unsafeTheory :: [Datatype] -> [(Name, TheoryDefinition)] -> Theory
unsafeTheory datatypes definitions = either (error . show) id (theory datatypes definitions)
