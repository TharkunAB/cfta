{-# LANGUAGE OverloadedStrings #-}

{- | The geometric sequents over a theory of integer lists: the count of each
size, the Horn clauses of the small sizes, and the rank of one law.
-}
module Main (main) where

import Control.Monad (unless)
import Data.List (intercalate)
import qualified Data.Text as Text

import Data.CFTA.Formula (Formula (..), Name (..), Relation (..), Sort (..), Term (..), renderFormula)
import Data.CFTA.Gen.ManySorted.Scoped (scopedAutomaton)
import Data.CFTA.Gen.Refinement.Sequent
import Data.CFTA.Index (Cardinality (..), Size (..))
import Data.CFTA.Refinement.Sequent (Sequent (..), Shape (..), sequent, sequentFormula, shape)
import Data.CFTA.Refinement.Theory
import Data.CFTA.Sized (countOfSize, rankOfSize, sized, termsOfSize, unrankOfSize)

-- | The sort of integer lists.
list :: Sort
list = NamedSort "List" [IntSort]

-- | Integer lists with the functions @append@ and @reverse@.
lists :: Theory
lists = either (error . show) id (theory [lists'] [("append", append), ("reverse", reverse')])
  where
    lists' = Datatype list [Constructor "nil" [], Constructor "cons" [("item", IntSort), ("rest", list)]]
    -- The items of the left list, then the items of the right list.
    append =
        FunctionDefinition [("left", list), ("right", list)] list
            $ byCases "left" (Var "right")
            $ App "cons" [Var "first", App "append" [Var "others", Var "right"]]
    -- The items of the list in the other order.
    reverse' =
        FunctionDefinition [("items", list)] list
            $ byCases "items" nil
            $ App "append" [App "reverse" [Var "others"], App "cons" [Var "first", nil]]
    -- A split of a list: one term for the empty list, and one term for a first item and the others.
    byCases scrutinee empty nonEmpty =
        Split scrutinee [Branch "nil" [] (Expression empty), Branch "cons" ["first", "others"] (Expression nonEmpty)]

-- | The empty list.
nil :: Term
nil = App "nil" []

-- | Equality at both sorts, the literal 0, binders at both sorts, and at most three binders.
settings :: SequentSettings
settings =
    SequentSettings
        { sequentRelations = [(IntSort, [Eq]), (list, [Eq])]
        , sequentLiterals = [0]
        , sequentBinderSorts = [IntSort, list]
        , sequentBinders = 3
        }

-- | Each list is empty or a cons: a sequent with an empty body and two disjuncts.
cases :: Sequent
cases =
    Sequent
        [("xs", list)]
        []
        [([], [Atom Eq (Var "xs") nil]), ([("h", IntSort), ("t", list)], [Atom Eq (Var "xs") (App "cons" [Var "h", Var "t"])])]

-- | A sequent as text, as in @forall (x0 : List Int). a && b ==> c || exists (x1 : Int). d@.
render :: Sequent -> String
render (Sequent bound body heads) = binders "forall" bound <> atoms body <> " ==> " <> disjuncts
  where
    binders _ [] = ""
    binders word names =
        word <> " " <> unwords ["(" <> Text.unpack name <> " : " <> sortText sort <> ")" | (Name name, sort) <- names] <> ". "
    atoms [] = "true"
    atoms parts = intercalate " && " (map renderFormula parts)
    disjuncts
        | null heads = "false"
        | otherwise = intercalate " || " [binders "exists" names <> atoms parts | (names, parts) <- heads]
    sortText (NamedSort (Name name) arguments) = unwords (Text.unpack name : map sortText arguments)
    sortText IntSort = "Int"
    sortText other = show other

-- | Stop with a message when a value is not the expected value.
check :: (Eq a, Show a) => String -> a -> a -> IO ()
check label expected actual = unless (actual == expected) $ fail $ label <> ": expected " <> show expected <> ", got " <> show actual

-- | Count, list, rank, and read back the sequents, and check each printed value.
main :: IO ()
main = do
    let signature = sequentSignature lists settings
    automaton <- either (fail . show) pure (scopedAutomaton sequentCodec signature)
    classes <- either (fail . show) pure (sized automaton)

    let counts = [count | size <- [1 .. 20], let Cardinality count = countOfSize classes (Size size)]
    putStrLn $ "Sequents of the sizes 1 to 20: " <> show counts
    check
        "counts"
        [0, 0, 1, 2, 4, 8, 2, 12, 55, 233, 630, 2656, 8531, 35252, 130549, 544240, 2146010, 9058376, 37522096, 161279464]
        counts

    -- The Horn clauses bind only lists, so fewer of them differ only in the sorts of unused binders.
    listAutomaton <-
        either (fail . show) pure (scopedAutomaton sequentCodec (sequentSignature lists settings{sequentBinderSorts = [list]}))
    listClasses <- either (fail . show) pure (sized listAutomaton)
    let horn = [s | size <- [1 .. 8], term <- termsOfSize listClasses (Size size), Just s <- [readSequent term], shape s == Horn]
    putStrLn $ "Horn clauses up to the size 8, with binders of the sort List only: " <> show (length horn)
    mapM_ (putStrLn . ("  " <>) . render) horn
    check "Horn clauses" 13 (length horn)
    check "binder sorts of the Horn clauses" [] [s | s <- horn, any ((/= list) . snd) (sequentBound s)]
    check "Horn clauses that the formula gives again" [] [s | s <- horn, sequent (sequentFormula s) /= Right s]

    term <- either (fail . show) pure (writeSequent signature cases)
    let ranked = rankOfSize classes term
    putStrLn $ "The rank of " <> render cases <> ": " <> show ranked
    check "rank" (Just (20, 134284394)) ranked
    back <-
        maybe
            (fail "no rank")
            (\(size, rank) -> maybe (fail "no term at the rank") pure (unrankOfSize classes size rank))
            ranked
    check "term at the rank" term back
    let readBack = readSequent back
    putStrLn $ "The sequent at that rank: " <> maybe "none" render readBack
    check
        "sequent at the rank"
        ( Just $
            Sequent
                [("x0", list)]
                []
                [ ([], [Atom Eq (Var "x0") nil])
                , ([("x1", IntSort), ("x2", list)], [Atom Eq (Var "x0") (App "cons" [Var "x1", Var "x2"])])
                ]
        )
        readBack
