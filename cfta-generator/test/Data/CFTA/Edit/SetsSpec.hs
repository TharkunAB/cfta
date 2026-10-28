module Data.CFTA.Edit.SetsSpec (spec) where

import Data.Containers.ListUtils (nubOrd)
import Data.List (isPrefixOf, subsequences)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import Test.Hspec (Spec, describe, it, shouldBe)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, noConstraint)
import Data.CFTA.Edit
import Data.CFTA.Edit.Sets
import qualified Data.CFTA.Gen as Gen
import Data.CFTA.Index (ChildIndex (..), Size (..), TransitionIndex (..))
import Data.CFTA.Interned (fromFTA)
import Data.CFTA.Path (Path, path, unPath)
import Data.CFTA.Sized (countOfSize, sized, termsOfSize)
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

spec :: Spec
spec = describe "Data.CFTA.Edit.Sets" $ do
    it "gives the edit sets of the definition, for one to three edits" $
        mapM_
            ( \(name, automaton, given) ->
                mapM_
                    ( \k -> do
                        let expected = definition k automaton given
                        ((name, k, Set.size expected > 5), found k automaton given) `shouldBe` ((name, k, True), expected)
                    )
                    [1, 2, 3]
            )
            fixtures
    it "has one run for each edit set, and the generator counts them as the size classes do" $
        mapM_
            ( \(name, automaton, given) ->
                mapM_
                    ( \k -> do
                        let sets = setsOf k automaton given
                            classes = either (error . show) id $ sized sets
                            generator = Gen.fromAutomaton $ fromFTA sets
                            terms = [found' | size <- [1 .. limit k], found' <- termsOfSize classes (Size size)]
                        ((name, k, not (null terms)), [found' | found' <- terms, runs sets found' /= 1]) `shouldBe` ((name, k, True), [])
                        ( (name, k)
                            , and [Gen.countAtSize generator (Size size) == Right (countOfSize classes (Size size)) | size <- [1 .. limit k]]
                            )
                            `shouldBe` ((name, k), True)
                    )
                    [1, 2, 3]
            )
            fixtures
    it "has the size classes of the edit automaton for one edit" $
        mapM_
            ( \(name, automaton, given) -> do
                let single = either (error . show) id $ sized $ setsOf 1 automaton given
                    edits = either (error . show) id $ sized $ either (error . show) id $ editAutomaton automaton given
                (name, [countOfSize single (Size size) | size <- [1 .. bound + 1]])
                    `shouldBe` (name, [countOfSize edits (Size size) | size <- [1 .. bound + 1]])
            )
            fixtures
    it "applies an edit set at incomparable paths, in any order" $
        mapM_
            ( \(name, automaton, given) -> do
                let sets = setsOf 3 automaton given
                    classes = either (error . show) id $ sized sets
                    terms = [found' | size <- [1 .. limit 3], found' <- termsOfSize classes (Size size)]
                    results =
                        [ (applyEditSet given set, foldM' given (reverse edits), length edits, paths)
                        | set <- terms
                        , Just edits <- [editsOfSet set]
                        , let paths = [unPath (sitePath site) | Term.Node site _ <- edits]
                        ]
                (name, not (null results)) `shouldBe` (name, True)
                ( name
                    , [ r
                      | r@(applied, reversed, count, paths) <- results
                      , applied == Nothing || applied /= reversed || count > 3 || not (incomparable paths)
                      ]
                    )
                    `shouldBe` (name, [])
            )
            fixtures
    it "gives the sites of the automaton in one run to a set of three" $
        -- Three sites that no other order of the preorder can name.
        let given =
                Term.Node "g" [Term.Node "g" [Term.Node "a" [], Term.Node "a" []], Term.Node "g" [Term.Node "a" [], Term.Node "a" []]]
            set =
                Term.Node
                    (Link $ ReplaceAt $ path [0, 0])
                    [ Term.Node (Inside $ Material "b") []
                    , Term.Node
                        (Link $ ReplaceAt $ path [0, 1])
                        [Term.Node (Inside $ Material "b") [], Term.Node (Last $ ReplaceAt $ path [1]) [Term.Node (Inside $ Material "b") []]]
                    ]
            sets = setsOf 3 trees given
         in (runs sets set, applyEditSet given set)
                `shouldBe` (1, Just (Term.Node "g" [Term.Node "g" [Term.Node "b" [], Term.Node "b" []], Term.Node "b" []]))
  where
    foldM' term' edits = foldl (\current edit -> current >>= \t -> applyEdit t edit) (Just term') edits
    incomparable paths = and [not (a `isPrefixOf` b) | a <- paths, b <- paths, a /= b]

-- | The largest total new material that the tests compare.
bound :: Integer
bound = 3

-- | The largest size of an edit set with the new material up to the bound: one node for each edit.
limit :: Int -> Integer
limit k = bound + toInteger k

setsOf :: Int -> FTA.PlainFTA String String -> Term String -> FTA.PlainFTA (SetState String String) (SetSymbol String)
setsOf k automaton given = either (error . show) id $ editSetAutomaton k automaton given

-- | The edit sets of the automaton with the total new material up to the bound.
found :: Int -> FTA.PlainFTA String String -> Term String -> Set.Set (Set.Set (Edit String))
found k automaton given =
    Set.fromList
        [ Set.fromList edits
        | size <- [1 .. limit k]
        , set <- termsOfSize classes (Size size)
        , Just edits <- [editsOfSet set]
        , sum [toInteger (length edit) - 1 | edit <- edits] <= bound
        ]
  where
    classes = either (error . show) id $ sized $ setsOf k automaton given

{- | The edit sets by the definition: the sets of one to k edits at pairwise
incomparable positions, where an edit at a position is a replacement by
another term of the state of the position, or a wrap in a transition of that
state with the old subterm as a child that accepts it, and the other children
terms of their states. The new material is up to the bound in total.
-}
definition :: Int -> FTA.PlainFTA String String -> Term String -> Set.Set (Set.Set (Edit String))
definition k automaton given =
    Set.fromList
        [ Set.fromList chosen
        | places <- subsequences (positions given)
        , not (null places)
        , length places <= k
        , and [not (left `isPrefixOf` right) | left <- places, right <- places, left /= right]
        , chosen <- traverse editsAt places
        , sum [toInteger (length edit) - 1 | edit <- chosen] <= bound
        ]
  where
    editsAt at =
        [ Term.Node (ReplaceAt $ path $ map ChildIndex at) [fmap Material new]
        | new <- termsOf state (fromInteger bound)
        , new /= old
        ]
            <> [ Term.Node
                    (WrapAt (path $ map ChildIndex at) symbol (TransitionIndex index) (ChildIndex hole))
                    (map (fmap Material) siblings)
               | (index, FTA.Transition symbol children _) <- zip [0 ..] $ FTA.transitionsFrom automaton state
               , (hole, child) <- zip [0 ..] children
               , acceptsAt child old
               , siblings <- siblingTerms [sibling | (other, sibling) <- zip [0 :: Int ..] children, other /= hole]
               ]
      where
        old = fromMaybe (error "no subterm") $ subtermAt given at
        state = runState at
    siblingTerms [] = [[]]
    siblingTerms (state : rest) = [new : others | new <- termsOf state (fromInteger bound), others <- siblingTerms rest]
    termsOf state size = [candidate | candidate <- allTerms automaton =<< [1 .. size], acceptsAt state candidate]
    runState at = case [ state
                       | state <- FTA.states automaton
                       , Just old <- [subtermAt given at]
                       , acceptsAt state old
                       , Just holed <- [replaceAt given at (Term.Node "hole" [])]
                       , FTA.accepts (withHole state) holed
                       ] of
        [state] -> state
        states -> error $ "not one run state: " <> show states
    withHole state = fromRows (FTA.initialState automaton) $ (state, [leaf "hole"]) : Map.toList (FTA.transitionTable automaton)
    acceptsAt state = FTA.accepts (rooted Map.! state)
    rooted = Map.fromList [(state, fromRows state $ Map.toList $ FTA.transitionTable automaton) | state <- FTA.states automaton]

-- | The fixtures: an unambiguous automaton and a term that it accepts.
fixtures :: [(String, FTA.PlainFTA String String, Term String)]
fixtures =
    [ ("expressions", expressions, Term.Node "add" [lit "one", Term.Node "neg" [lit "two"]])
    ,
        ( "binary trees over a and b"
        , trees
        , Term.Node "g" [Term.Node "g" [Term.Node "a" [], Term.Node "b" []], Term.Node "a" []]
        )
    , ("a balanced tree of 7 nodes", trees, Term.Node "g" [Term.Node "g" [leafA, leafA], Term.Node "g" [leafA, leafA]])
    ]
  where
    leafA = Term.Node "a" []

trees :: FTA.PlainFTA String String
trees = fromRows "s" [("s", [leaf "a", leaf "b", node "g" ["s", "s"]])]

-- | Expressions: a literal of a number, a negation, or a sum.
expressions :: FTA.PlainFTA String String
expressions = fromRows "e" [("e", [node "lit" ["n"], node "neg" ["e"], node "add" ["e", "e"]]), ("n", [leaf "one", leaf "two"])]

-- | A literal of a number.
lit :: String -> Term String
lit number = Term.Node "lit" [Term.Node number []]

-- | The number of runs of an automaton on a term.
runs :: (Ord state, Eq symbol) => FTA.PlainFTA state symbol -> Term symbol -> Integer
runs automaton = go (FTA.initialState automaton)
  where
    go state (Term.Node symbol children) =
        sum
            [ product (zipWith go childStates children)
            | FTA.Transition other childStates _ <- FTA.transitionsFrom automaton state
            , other == symbol
            , length childStates == length children
            ]

-- | The path of an edit site.
sitePath :: EditSymbol symbol -> Path
sitePath symbol = case symbol of
    ReplaceAt at -> at
    WrapAt at _ _ _ -> at
    Material _ -> mempty

-- | The positions of a term, the root first.
positions :: Term String -> [[Int]]
positions (Term.Node _ children) = [] : [index : at | (index, child) <- zip [0 ..] children, at <- positions child]

-- | The subterm at a position.
subtermAt :: Term String -> [Int] -> Maybe (Term String)
subtermAt found' [] = Just found'
subtermAt (Term.Node _ children) (index : rest) = case drop index children of
    child : _ -> subtermAt child rest
    [] -> Nothing

-- | The term with the subterm at a position replaced.
replaceAt :: Term String -> [Int] -> Term String -> Maybe (Term String)
replaceAt _ [] new = Just new
replaceAt (Term.Node symbol children) (index : rest) new = case splitAt index children of
    (before, child : after) -> (\changed -> Term.Node symbol (before <> (changed : after))) <$> replaceAt child rest new
    _ -> Nothing

-- | Every term of the given size over the symbols of the automaton.
allTerms :: FTA.PlainFTA String String -> Int -> [Term String]
allTerms automaton = go
  where
    symbols =
        nubOrd
            [ (FTA.transitionSymbol transition, length $ FTA.transitionChildren transition)
            | transitions <- Map.elems $ FTA.transitionTable automaton
            , transition <- transitions
            ]
    go size = [Term.Node symbol children | (symbol, arity) <- symbols, children <- spread arity (size - 1)]
    spread 0 0 = [[]]
    spread 0 _ = []
    spread arity remaining =
        [ first : rest
        | firstSize <- [1 .. remaining - (arity - 1)]
        , first <- go firstSize
        , rest <- spread (arity - 1) (remaining - firstSize)
        ]

-- | An automaton from rows of named states.
fromRows :: String -> [(String, [FTA.Transition String String Constraint])] -> FTA.PlainFTA String String
fromRows initial rows = either (error . show) id $ FTA.mkFTA initial rows

-- | A transition without children.
leaf :: String -> FTA.Transition String String Constraint
leaf symbol = FTA.Transition symbol [] noConstraint

-- | A transition without a constraint.
node :: String -> [String] -> FTA.Transition String String Constraint
node symbol children = FTA.Transition symbol children noConstraint
