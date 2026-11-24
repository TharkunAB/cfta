{-# LANGUAGE OverloadedStrings #-}

{- | Review an update of a language before keeping it.

The language has arithmetic expressions: @add@ with two children, @neg@ with
one child, @zero@, and @one@. Four named exclusions remove terms that have a
simpler form. The program asks three questions that have an exact answer:
what each exclusion removes alone, which term shows it, and whether an update
keeps the verdicts of a list of example terms. The program checks each value
that it prints.
-}
module Main (main) where

import Control.Monad (forM_, unless)
import qualified Data.Map.Strict as Map
import Data.String (fromString)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (equalityConstraint)
import Data.CFTA.Equality.Constraint (mkEqConstraints)
import Data.CFTA.Inclusion (Inclusion (..), InclusionError (..), inclusion, inclusionUpTo)
import Data.CFTA.Index (Cardinality (..), Size (..))
import Data.CFTA.Language (Language)
import qualified Data.CFTA.Language as L
import qualified Data.CFTA.Language.Source as D
import Data.CFTA.Path (path)
import Data.CFTA.Sized (countOfSize, sized)
import Data.CFTA.Symbol (Symbol)
import Data.CFTA.Template (Exclusion (..), Template (..))
import Data.CFTA.Term (Term (Node))

-- | The size bound of every count. The size of a term is its number of nodes.
bound :: Integer
bound = 9

-- | The language without exclusions.
original :: Language String
original =
    L.fromDocument
        $ either (error . D.explainDocumentError) id
        $ D.mkDocument
            "expr"
            [
                ( "expr"
                ,
                    [ production "add" ["expr", "expr"]
                    , production "neg" ["expr"]
                    , production "zero" []
                    , production "one" []
                    ]
                )
            ]
  where
    production name children =
        FTA.Transition (fromString name) children $
            D.Annotation (fromString name) Map.empty

-- | The named exclusions. Each one removes the terms that contain its template.
rules :: [(L.ExclusionName, Exclusion Symbol)]
rules =
    [ ("double-neg", Anywhere $ TemplateNode "neg" [TemplateNode "neg" [Hole]])
    , ("add-zero-left", Anywhere $ TemplateNode "add" [TemplateNode "zero" [], Hole])
    , ("neg-zero", Anywhere $ TemplateNode "neg" [TemplateNode "zero" []])
    , ("neg-neg-zero", Anywhere $ TemplateNode "neg" [TemplateNode "neg" [TemplateNode "zero" []]])
    ]

-- | Apply an update. An invalid update is an error of the program.
apply :: Language String -> L.Update String -> Language String
apply language = either (error . L.explainUpdateError) id . L.update language

-- | The number of terms of the language with at most 'bound' nodes.
count :: Language String -> Integer
count language = case sized (L.compileGraph language) of
    Left failure -> error (show failure)
    Right classes -> sum [n | size <- [1 .. bound], let Cardinality n = countOfSize classes (Size size)]

-- | The language with every named exclusion.
full :: Language String
full = apply original $ mconcat [L.without name rule | (name, rule) <- rules]

-- | The terms that must be members of the language.
members :: [Term Symbol]
members = [Node "add" [Node "one" [], Node "zero" []], Node "neg" [Node "one" []]]

-- | The terms that must not be members of the language.
nonMembers :: [Term Symbol]
nonMembers = [Node "neg" [Node "neg" [Node "one" []]]]

{- | The examples that an update changes, each with its new verdict.
An example is a member or a non-member, as the lists above say.
-}
changedExamples :: Language String -> Language String -> [(Term Symbol, Bool)]
changedExamples before after =
    [ (term, verdict)
    | term <- members <> nonMembers
    , let verdict = accepted after term
    , verdict /= accepted before term
    ]
  where
    accepted language = FTA.accepts (L.compileGraph language)

-- | The term that an inclusion check gives as a counterexample, if any.
smallestTerm :: Inclusion Symbol -> Maybe (Term Symbol)
smallestTerm result = case result of
    NotIncluded term -> Just term
    _ -> Nothing

-- | Check a condition, and stop the program with a message when it fails.
check :: String -> Bool -> IO ()
check message ok = unless ok $ fail message

-- | Run the three questions. Each answer is checked against its expected value.
main :: IO ()
main = do
    putStrLn "question 1 and 2: what does each exclusion remove alone?"
    let allCount = count full
    putStrLn $
        "terms up to size "
            <> show bound
            <> ": "
            <> show (count original)
            <> " without exclusions, "
            <> show allCount
            <> " with all"
    check "wrong counts" (count original == 5698 && allCount == 695)
    let expected =
            [ ("double-neg", 615, NotIncluded $ Node "neg" [Node "neg" [Node "one" []]])
            , ("add-zero-left", 1308, NotIncluded $ Node "add" [Node "zero" [], Node "one" []])
            , ("neg-zero", 665, NotIncluded $ Node "neg" [Node "zero" []])
            , ("neg-neg-zero", 0, Included)
            ]
    forM_ (zip rules expected) $ \((name, _), (expectedName, expectedGain, expectedWitness)) -> do
        let without = apply full (L.restore name)
            gain = count without - allCount
            shown = L.exclusionNameText name
        witness <- either (fail . show) pure $ inclusion (L.compileGraph without) (L.compileGraph full)
        putStrLn $
            "  "
                <> show shown
                <> ": removes "
                <> show gain
                <> " terms alone; "
                <> case witness of
                    NotIncluded term -> "smallest term that only it removes: " <> show term
                    Included -> "redundant: the other exclusions remove every term that it removes"
                    IncludedUpTo size -> "no such term up to " <> show size
                    UnknownAt size -> "no answer at " <> show size
        check ("wrong name " <> show shown) (shown == expectedName)
        check ("wrong count for " <> show shown) (gain == expectedGain)
        check ("wrong answer of inclusion for " <> show shown) (witness == expectedWitness)

    putStrLn "question 3: does an update keep the examples?"
    let keep = L.without "no-add-one-one" $ Anywhere $ TemplateNode "add" [TemplateNode "one" [], TemplateNode "one" []]
        drop' = L.without "no-neg-one" $ Anywhere $ TemplateNode "neg" [TemplateNode "one" []]
    forM_ [("no-add-one-one", keep), ("no-neg-one", drop')] $ \(name, change) -> do
        let changed = changedExamples full (apply full change)
        putStrLn $
            "  update "
                <> show (name :: String)
                <> ": "
                <> if null changed then "keeps every example" else "refused, changes " <> show changed
    check "wrong verdicts of the first update" (null $ changedExamples full $ apply full keep)
    check
        "wrong verdicts of the second update"
        (changedExamples full (apply full drop') == [(Node "neg" [Node "one" []], False)])

    putStrLn "a fact: the same questions, with relax in place of restore"
    let twin = L.at "expr" "twin"
        sameChildren = equalityConstraint $ mkEqConstraints [[path [0], path [1]]]
        withTwin = apply full $ L.define twin "twin" ["expr", "expr"] <> L.require twin "same-children" sameChildren
        relaxed = apply withTwin $ L.relax twin "same-children"
        factGain = count relaxed - count withTwin
    factWitness <- either (fail . show) pure $ inclusionUpTo (Size bound) (L.compileGraph relaxed) (L.compileGraph withTwin)
    putStrLn $
        "  \"same-children\": removes "
            <> show factGain
            <> " terms alone; smallest term that only it removes: "
            <> maybe "none" show (smallestTerm factWitness)
    check "wrong count for the fact" (factGain == 9606)
    check "wrong term for the fact" (smallestTerm factWitness == Just (Node "twin" [Node "one" [], Node "zero" []]))
    -- 'inclusion' has no bound and refuses an automaton with a constraint.
    check
        "inclusion did not refuse the constraint"
        (inclusion (L.compileGraph relaxed) (L.compileGraph withTwin) == Left ConstrainedRight)
    putStrLn "  inclusion without a bound refuses the constraint: ConstrainedRight"
