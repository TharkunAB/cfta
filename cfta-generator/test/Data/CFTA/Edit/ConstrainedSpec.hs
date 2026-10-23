module Data.CFTA.Edit.ConstrainedSpec (spec) where

import Control.Monad (filterM, forM, zipWithM)
import Data.Containers.ListUtils (nubOrd)
import Data.Functor.Identity (runIdentity)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.String (fromString)
import Test.Hspec (Spec, describe, it, shouldBe)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (
    Constraint (..),
    Guard (..),
    equalitiesHold,
    equalityConstraint,
    noConstraint,
    semanticConstraint,
 )
import Data.CFTA.Edit
import Data.CFTA.Edit.Constrained
import Data.CFTA.Equality.Constraint (mkEqConstraints)
import qualified Data.CFTA.Formula as Formula
import qualified Data.CFTA.Gen as Gen
import Data.CFTA.Index (ChildIndex (..), Size (..), TransitionIndex (..))
import Data.CFTA.Interned (fromFTA)
import Data.CFTA.Path (path)
import Data.CFTA.Refinement.Evaluate (evaluateConstraint)
import Data.CFTA.Refinement.Expression (Formula, refinementFormula, (.==), (.>))
import Data.CFTA.Refinement.Verdict (Entailment (Entailment), Verdict (..), negateVerdict)
import Data.CFTA.Sized (SizedError (..), countOfSize, sized, sizedUpTo, termsOfSize)
import Data.CFTA.Symbol (Symbol (RefinedSymbol))
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

spec :: Spec
spec = describe "Data.CFTA.Edit.Constrained" $ do
    it "gives each edited term as often as the definition does, without the sites it leaves out" $
        -- The fixture with two transitions for one symbol has its own tests below.
        [(name, decoded automaton given) | (name, automaton, given) <- fixtures, name /= "two runs"]
            `shouldBe` [ (name, definition (map fst $ expectedLeftOut name) automaton given)
                       | (name, automaton, given) <- fixtures
                       , name /= "two runs"
                       ]
    it "leaves out the context wraps whose hole a constraint can read" $
        [ (name, leftOut <$> constrainedEditAutomaton automaton given) | (name, automaton, given) <- fixtures, name /= "two runs"
        ]
            `shouldBe` [(name, Right $ expectedLeftOut name) | (name, _, _) <- fixtures, name /= "two runs"]
    it "has edits of each kind that the definition checks" $
        [ ( name
          , Set.fromList
                [ kindOf edit
                | size <- [1 .. bound + 1]
                , edit <- termsOfSize (classesOf automaton given) (Size size)
                , Just edited <- [applyEdit given edit]
                , toInteger (length edited) <= bound
                ]
          )
        | (name, automaton, given) <- fixtures
        , name `elem` ["chains beside an equal pair", "pairs of chains"]
        ]
            `shouldBe` [ ("chains beside an equal pair", Set.fromList ["replace", "unwrap", "wrap", "context"])
                       , ("pairs of chains", Set.fromList ["replace", "unwrap", "wrap"])
                       ]
    it "unwraps a subterm only when its classes still hold" $
        [edit | edit <- termsOfSize (classesOf pairsOfChains pairsOfChainsTerm) 1, kindOf edit == "unwrap"]
            `shouldBe` [Term.Node (UnwrapAt (path [0]) (ChildIndex index)) [] | index <- [0, 1]]
    it "has one run for each edit" $
        [ ( name
          , [ edit
            | size <- [1 .. bound + 1]
            , edit <- termsOfSize (classesOf automaton given) (Size size)
            , runs (editsFor automaton given) edit /= 1
            ]
          )
        | (name, automaton, given) <- fixtures
        ]
            `shouldBe` [(name, []) | (name, _, _) <- fixtures]
    it "pins a child to the fixed subterm of its class" $
        termsOfSize (classesOf pinned pinnedTerm) 3
            `shouldBe` [Term.Node (ReplaceAt $ path [0]) [material "h" [material "a" []]]]
    it "moves a class of paths into a child onto the edit" $
        [ FTA.transitionConstraint transition
        | transition <- FTA.transitionsFrom (editsFor shifted shiftedTerm) ConstrainedRoot
        , FTA.transitionSymbol transition == ReplaceAt (path [0])
        ]
            `shouldBe` [equalityConstraint $ mkEqConstraints [[path [0, 0], path [0, 1]]]]
    it "pins the other child of a wrap to the old subterm" $
        [edit | edit <- termsOfSize (classesOf wrapping wrappingTerm) 2, isWrap edit]
            `shouldBe` [Term.Node (WrapAt (path [0]) "pair" 2 (ChildIndex hole)) [material "a" []] | hole <- [0, 1]]
    it "counts the edits as the generator does when the edit automaton is acyclic" $
        -- The acyclic import counts the finite language, by other sizes, so
        -- the totals are compared. No edit of these fixtures has 20 nodes.
        [ (name, Gen.cardinality $ Gen.fromAutomaton $ fromFTA $ editsFor automaton given)
        | (name, automaton, given) <- fixtures
        , name `elem` acyclic
        ]
            `shouldBe` [ (name, Right $ sum [countOfSize (classesOf automaton given) (Size size) | size <- [1 .. 20]])
                       | (name, automaton, given) <- fixtures
                       , name `elem` acyclic
                       ]
    it "leaves a cyclic edit automaton with equality constraints to the size classes" $
        [ (name, Gen.countAtSize (Gen.fromAutomaton $ fromFTA $ editsFor automaton given) 3)
        | (name, automaton, given) <- fixtures
        , name `elem` ["equal chains", "pairs that wrap"]
        ]
            `shouldBe` [(name, Left Gen.CannotCountConstrainedEdges) | name <- ["equal chains", "pairs that wrap"]]
    describe "with two transitions for one symbol above a site" $ do
        -- g(a, b) is a replacement of the second a, which the transition g(v, w)
        -- accepts. The transition of the run, g(x, x) with equal children,
        -- would pin the new child to a and so leave the edit out.
        it "lists the sites below the state apart" $
            fmap leftOut (constrainedEditAutomaton twoRuns twoRunsTerm)
                `shouldBe` Right [(ReplaceAt $ path [0], Branching), (ReplaceAt $ path [1], Branching)]
        it "needs the list: the definition has an edit there that the run of the term does not show" $ do
            Map.lookup (term "g" [term "a" [], term "b" []]) (definition [] twoRuns twoRunsTerm) `shouldBe` Just 2
            Map.lookup (term "g" [term "a" [], term "b" []]) (decoded twoRuns twoRunsTerm) `shouldBe` Just 1
        it "gives the edits of the other sites as the definition does" $
            decoded twoRuns twoRunsTerm `shouldBe` definition [ReplaceAt $ path [0], ReplaceAt $ path [1]] twoRuns twoRunsTerm
    describe "with guards" $ do
        it "gives each edited term as often as the definition does, with a solver that decides every guard" $ do
            found <- forM guardFixtures $ \(name, automaton, given) -> do
                pairs <- guardedEdits fullSolver automaton given
                pure (name, Map.fromListWith (+) [(edited, 1) | (_, edited) <- pairs])
            expected <- forM guardFixtures $ \(name, automaton, given) -> do
                counted <- definitionWith (decidedBy fullSolver) (map fst $ expectedGuardLeftOut name) automaton given
                pure (name, counted)
            found `shouldBe` expected
        it "leaves out the sites of an atom on fixed paths and new material, and the context wraps whose hole a guard can read" $ do
            found <- forM guardFixtures $ \(name, automaton, given) -> do
                result <- guardedEditAutomaton fullSolver automaton given
                pure (name, leftOut <$> result)
            found `shouldBe` [(name, Right $ expectedGuardLeftOut name) | (name, _, _) <- guardFixtures]
        it "has edits of each kind that the definition checks" $ do
            found <- forM [fixture | fixture@(name, _, _) <- guardFixtures, name `elem` ["guarded chains", "guarded pairs"]] $
                \(name, automaton, given) -> do
                    pairs <- guardedEdits fullSolver automaton given
                    pure (name, Set.fromList [kindOf edit | (edit, _) <- pairs])
            found
                `shouldBe` [ ("guarded chains", Set.fromList ["replace", "unwrap", "wrap", "context"])
                           , ("guarded pairs", Set.fromList ["replace", "wrap"])
                           ]
        it "decides an atom on fixed paths once, and moves an atom on the new material onto the edit" $ do
            result <- either (error . show) id <$> guardedEditAutomaton fullSolver (leafGuard aboveOneAt00) leafTerm
            [ (FTA.transitionSymbol transition, constraintGuard $ FTA.transitionConstraint transition)
              | transition <- FTA.transitionsFrom (edits result) ConstrainedRoot
              , FTA.transitionSymbol transition `elem` [ReplaceAt $ path [0, 0], ReplaceAt $ path [1]]
              ]
                `shouldBe` [(ReplaceAt $ path [0, 0], Satisfies (path [0]) aboveOne), (ReplaceAt $ path [1], Top)]
        it "lists a site apart when the solver does not decide an atom on fixed paths, or the fixed part of the site" $ do
            eitherLeaf <-
                guardedEditAutomaton partialSolver (leafGuard eitherAboveOne) (symbolTerm "g" [symbolTerm "f" [number 2], number 3])
            unwraps <- guardedEditAutomaton partialSolver guardedUnwraps guardedUnwrapsTerm
            (leftOut <$> eitherLeaf, leftOut <$> unwraps)
                `shouldBe` ( Right [(ReplaceAt $ path [0], UndecidedGuard), (ReplaceAt $ path [0, 0], UndecidedGuard)]
                           , Right [(UnwrapAt (path [0]) 0, UndecidedGuard)]
                           )
        it "leaves an atom on the new material that the solver does not decide to the count" $ do
            result <- either (error . show) id <$> guardedEditAutomaton partialSolver (leafGuard aboveOneAt00) leafTerm
            counted <- sizedUpTo partialSolver 4 (fst $ plainSymbols $ edits result)
            either (\failure -> case failure of GuardUnknown _ _ -> "unknown"; _ -> "other") (const "decided") counted
                `shouldBe` "unknown"
  where
    isWrap edit = kindOf edit == "wrap"
    acyclic = ["pinned", "shifted", "equal pairs", "two runs"]

-- | The largest edited term that the tests check.
bound :: Integer
bound = 7

-- | The automata with equality constraints, each with a name and a term that it accepts.
fixtures :: [(String, FTA.PlainFTA String String, Term String)]
fixtures =
    [ ("pinned", pinned, pinnedTerm)
    , ("shifted", shifted, shiftedTerm)
    ,
        ( "equal pairs"
        , fromRows "s" [("s", [equalAt "g" ["q", "q"] [0] [1]]), ("q", [leaf "a", leaf "b"])]
        , term "g" [term "a" [], term "a" []]
        )
    ,
        ( "equal chains"
        , fromRows "s" [("s", [equalAt "g" ["c", "c"] [0] [1]]), ("c", [leaf "a", node "f" ["c"]])]
        , term "g" [term "f" [term "a" []], term "f" [term "a" []]]
        )
    , ("pairs that wrap", wrapping, wrappingTerm)
    ,
        ( "chains beside an equal pair"
        , fromRows
            "s"
            [("s", [equalAt "g" ["c", "x", "x"] [1] [2]]), ("c", [leaf "a", node "f" ["c"]]), ("x", [leaf "a", leaf "b"])]
        , term "g" [term "f" [term "a" []], term "b" [], term "b" []]
        )
    , ("pairs of chains", pairsOfChains, pairsOfChainsTerm)
    , ("two runs", twoRuns, twoRunsTerm)
    ]

-- | The sites that the edit automaton of each fixture leaves out.
expectedLeftOut :: String -> [(EditSymbol String, LeftOut)]
expectedLeftOut name = case name of
    "pairs that wrap" -> [(ContextAt (path [0]) "pair" 2 (ChildIndex hole), ConstrainedHole) | hole <- [0, 1]]
    "pairs of chains" ->
        (ContextAt (path [0]) "f" 1 0, ConstrainedHole)
            : [(ContextAt (path [0]) "pair" 2 (ChildIndex hole), ConstrainedHole) | hole <- [0, 1]]
    _ -> []

-- | k(c) where c is a, f(c), or a pair of equal terms of c.
pairsOfChains :: FTA.PlainFTA String String
pairsOfChains = fromRows "s" [("s", [node "k" ["c"]]), ("c", [leaf "a", node "f" ["c"], equalAt "pair" ["c", "c"] [0] [1]])]

-- | The term k(pair(f(a), f(a))).
pairsOfChainsTerm :: Term String
pairsOfChainsTerm = term "k" [term "pair" [term "f" [term "a" []], term "f" [term "a" []]]]

-- | The kind of the site of an edit.
kindOf :: Term (EditSymbol symbol) -> String
kindOf (Term.Node symbol _) = case symbol of
    ReplaceAt _ -> "replace"
    WrapAt{} -> "wrap"
    UnwrapAt{} -> "unwrap"
    ContextAt{} -> "context"
    HoleParent{} -> "material"
    Material _ -> "material"

-- | g(t, u) where the subterm of t below its root equals u.
pinned :: FTA.PlainFTA String String
pinned =
    fromRows
        "s"
        [ ("s", [equalAt "g" ["t", "u"] [0, 0] [1]])
        , ("t", [node "f" ["x"], node "h" ["x"]])
        , ("u", [leaf "a", leaf "b"])
        , ("x", [leaf "a", leaf "b"])
        ]

-- | The term g(f(a), a).
pinnedTerm :: Term String
pinnedTerm = term "g" [term "f" [term "a" []], term "a" []]

-- | w(pair(x, y)) where x equals y, with the class on the transition of w.
shifted :: FTA.PlainFTA String String
shifted = fromRows "s" [("s", [equalAt "w" ["p"] [0, 0] [0, 1]]), ("p", [node "pair" ["x", "x"]]), ("x", [leaf "a", leaf "b"])]

-- | The term w(pair(a, a)).
shiftedTerm :: Term String
shiftedTerm = term "w" [term "pair" [term "a" [], term "a" []]]

-- | k(c) where c is a leaf or a pair of equal terms of c.
wrapping :: FTA.PlainFTA String String
wrapping = fromRows "s" [("s", [node "k" ["c"]]), ("c", [leaf "a", leaf "b", equalAt "pair" ["c", "c"] [0] [1]])]

-- | The term k(a).
wrappingTerm :: Term String
wrappingTerm = term "k" [term "a" []]

-- | g(x, x) with equal children, or g(v, w): two transitions for g in one state.
twoRuns :: FTA.PlainFTA String String
twoRuns =
    fromRows
        "s"
        [ ("s", [equalAt "g" ["x", "x"] [0] [1], node "g" ["v", "w"]])
        , ("x", [leaf "a", leaf "b"])
        , ("v", [leaf "a"])
        , ("w", [leaf "b"])
        ]

-- | The term g(a, a).
twoRunsTerm :: Term String
twoRunsTerm = term "g" [term "a" [], term "a" []]

-- | The edit automaton of a fixture.
editsFor :: FTA.PlainFTA String String -> Term String -> FTA.PlainFTA ConstrainedState (EditSymbol String)
editsFor automaton given = either (error . show) edits $ constrainedEditAutomaton automaton given

-- | The size classes of the edits of a fixture.
classesOf :: FTA.PlainFTA String String -> Term String -> _
classesOf automaton given = either (error . show) id $ sized $ editsFor automaton given

-- | The edited terms of the edits up to one node more than 'bound', with the number of edits that give each.
decoded :: FTA.PlainFTA String String -> Term String -> Map.Map (Term String) Int
decoded automaton given =
    Map.fromListWith
        (+)
        [ (edited, 1)
        | size <- [1 .. bound + 1]
        , edit <- termsOfSize (classesOf automaton given) (Size size)
        , Just edited <- [applyEdit given edit]
        , toInteger (length edited) <= bound
        ]

-- | 'definitionWith' for an automaton with equality constraints.
definition :: [EditSymbol String] -> FTA.PlainFTA String String -> Term String -> Map.Map (Term String) Int
definition skipped automaton given =
    runIdentity $ definitionWith (\constraint subterm -> pure $ equalitiesHold constraint subterm) skipped automaton given

{- | The number of edits that give each candidate, by the definition: a
replacement, an unwrap, a wrap, or a context wrap at a position, in the state
that the run of the term gives the position, whose edited term the automaton
accepts. A context wrap counts once for each position of the old subterm in
the child with the hole. The first argument decides a constraint on a term.
The sites of the second argument are left out.
-}
definitionWith ::
    (Monad m, Ord symbol, Show symbol) =>
    (Constraint -> Term symbol -> m Bool) ->
    [EditSymbol symbol] ->
    FTA.PlainFTA String symbol ->
    Term symbol ->
    m (Map.Map (Term symbol) Int)
definitionWith check skipped automaton given = do
    found <- runsOf check automaton (FTA.initialState automaton) given
    let run = case found of
            [one] -> one
            _ -> error "not one run"
    counts <- forM (candidates automaton) $ \candidate -> do
        count <- editCount run candidate
        pure (candidate, count)
    pure $ Map.fromList [(candidate, count) | (candidate, count) <- counts, count > 0]
  where
    editCount run candidate = do
        accepted <- acceptsAt (FTA.initialState automaton) candidate
        if not accepted
            then pure 0
            else do
                found <-
                    forM
                        [ (path $ map ChildIndex at, state, old, new)
                        | (at, state) <- Map.toList run
                        , Just old <- [subtermAt given at]
                        , Just new <- [subtermAt candidate at]
                        , (replaceAt candidate at =<< subtermAt given at) == Just given
                        ]
                        (\(at, state, old, new) -> sites at state old new)
                pure $ length [site | site <- concat found, site `notElem` skipped]
    -- The sites at a position whose edit gives the new subterm.
    sites at state old@(Term.Node _ oldChildren) new@(Term.Node symbol arguments) = do
        accepted <- acceptsAt state new
        fitting <- map fst <$> filterM fits (zip [0 ..] (FTA.transitionsFrom automaton state))
        pure $
            [ReplaceAt at | new /= old, accepted]
                <> [UnwrapAt at (ChildIndex index) | (index, child) <- zip [0 ..] oldChildren, child == new, accepted]
                <> [ WrapAt at symbol (TransitionIndex index) (ChildIndex hole)
                   | index <- fitting
                   , (hole, argument) <- zip [0 ..] arguments
                   , argument == old
                   ]
                <> [ ContextAt at symbol (TransitionIndex index) (ChildIndex hole)
                   | index <- fitting
                   , (hole, argument) <- zip [0 ..] arguments
                   , place <- drop 1 $ positions argument
                   , subtermAt argument place == Just old
                   ]
      where
        -- Whether a transition of the state accepts the new subterm.
        fits (_, FTA.Transition other children constraint)
            | other /= symbol || length children /= length arguments = pure False
            | otherwise = do
                holds <- check constraint new
                childrenAccept <- zipWithM acceptsAt children arguments
                pure $ holds && and childrenAccept
    acceptsAt state =
        FTA.acceptsM
            (\_ transition subterm -> check (FTA.transitionConstraint transition) subterm)
            (fromRows state $ Map.toList $ FTA.transitionTable automaton)

-- | The positions of a term, the root first.
positions :: Term symbol -> [[Int]]
positions (Term.Node _ children) = [] : [index : at | (index, child) <- zip [0 ..] children, at <- positions child]

-- | The runs of an automaton from a state on a term: the state of each position. The first argument decides a constraint on a term.
runsOf ::
    (Monad m, Eq symbol) =>
    (Constraint -> Term symbol -> m Bool) -> FTA.PlainFTA String symbol -> String -> Term symbol -> m [Map.Map [Int] String]
runsOf check automaton state subterm@(Term.Node symbol children) =
    fmap concat $ forM (FTA.transitionsFrom automaton state) $ \(FTA.Transition other childStates constraint) -> do
        holds <- if other == symbol && length childStates == length children then check constraint subterm else pure False
        if not holds
            then pure []
            else do
                childRuns <- zipWithM (runsOf check automaton) childStates children
                pure
                    [ Map.insert [] state $ Map.unions [Map.mapKeys (index :) childRun | (index, childRun) <- zip [0 ..] picked]
                    | picked <- sequence childRuns
                    ]

-- | The number of runs of an edit automaton on an edit, with the equalities checked.
runs :: FTA.PlainFTA ConstrainedState (EditSymbol String) -> Term (EditSymbol String) -> Integer
runs automaton = go (FTA.initialState automaton)
  where
    go state found@(Term.Node symbol children) =
        sum
            [ product (zipWith go childStates children)
            | FTA.Transition other childStates constraint <- FTA.transitionsFrom automaton state
            , other == symbol
            , length childStates == length children
            , equalitiesHold constraint found
            ]

-- | The terms over the alphabet of the automaton with at most 'bound' nodes.
candidates :: (Ord symbol) => FTA.PlainFTA String symbol -> [Term symbol]
candidates automaton = allTerms =<< [1 .. fromInteger bound]
  where
    symbols =
        nubOrd
            [ (FTA.transitionSymbol transition, length $ FTA.transitionChildren transition)
            | transitions <- Map.elems $ FTA.transitionTable automaton
            , transition <- transitions
            ]
    allTerms size = [Term.Node symbol children | (symbol, arity) <- symbols, children <- spread arity (size - 1)]
    spread 0 0 = [[]]
    spread 0 _ = []
    spread arity remaining =
        [ first : rest
        | firstSize <- [1 .. remaining - (arity - 1)]
        , first <- allTerms firstSize
        , rest <- spread (arity - 1) (remaining - firstSize)
        ]

-- | The subterm at a position.
subtermAt :: Term symbol -> [Int] -> Maybe (Term symbol)
subtermAt found [] = Just found
subtermAt (Term.Node _ children) (index : rest) = case drop index children of
    child : _ -> subtermAt child rest
    [] -> Nothing

-- | The term with the subterm at a position replaced.
replaceAt :: Term symbol -> [Int] -> Term symbol -> Maybe (Term symbol)
replaceAt _ [] new = Just new
replaceAt (Term.Node symbol children) (index : rest) new = case splitAt index children of
    (before, child : after) -> (\changed -> Term.Node symbol (before <> (changed : after))) <$> replaceAt child rest new
    _ -> Nothing

-- | An automaton from rows of named states.
fromRows ::
    (Ord symbol, Show symbol) =>
    String -> [(String, [FTA.Transition String symbol Constraint])] -> FTA.PlainFTA String symbol
fromRows initial rows = either (error . show) id $ FTA.mkFTA initial rows

-- | A transition without children.
leaf :: String -> FTA.Transition String String Constraint
leaf symbol = FTA.Transition symbol [] noConstraint

-- | A transition without a constraint.
node :: String -> [String] -> FTA.Transition String String Constraint
node symbol children = FTA.Transition symbol children noConstraint

-- | A transition whose subterms at the two paths are equal.
equalAt :: String -> [String] -> [ChildIndex] -> [ChildIndex] -> FTA.Transition String String Constraint
equalAt symbol children one other = FTA.Transition symbol children $ equalityConstraint $ mkEqConstraints [[path one, path other]]

-- | A term from its symbol and children.
term :: String -> [Term String] -> Term String
term = Term.Node

-- | New material from its symbol and children.
material :: String -> [Term (EditSymbol String)] -> Term (EditSymbol String)
material = Term.Node . Material

-- | The automata with guards, each with a name and a term that it accepts.
guardFixtures :: [(String, FTA.PlainFTA String Symbol, Term Symbol)]
guardFixtures =
    [ ("a guard on a leaf", leafGuard aboveOneAt00, leafTerm)
    , ("either leaf above one", leafGuard eitherAboveOne, symbolTerm "g" [symbolTerm "f" [number 2], number 3])
    , ("a negated guard", leafGuard $ Not $ Satisfies (path [1]) aboveOne, leafTerm)
    , ("different leaves", leafGuard $ Not $ Same (path [0, 0]) (path [1]), leafTerm)
    ,
        ( "guarded chains"
        , fromRows
            "s"
            [ ("s", [guardedAt "g" ["c", "n"] $ Satisfies (path [1]) aboveOne])
            , ("c", [symbolNode "f" ["c"], symbolNode "h" ["n"]])
            , ("n", numbers)
            ]
        , symbolTerm "g" [symbolTerm "f" [symbolTerm "h" [number 2]], number 3]
        )
    ,
        ( "guarded pairs"
        , fromRows
            "s"
            [ ("s", [symbolNode "k" ["c"]])
            , ("c", numbers <> [guardedAt "pair" ["n", "c"] $ Satisfies (path [0]) aboveOne])
            , ("n", numbers)
            ]
        , symbolTerm "k" [number 2]
        )
    , ("guarded unwraps", guardedUnwraps, guardedUnwrapsTerm)
    ]

-- | The sites that the edit automaton of each fixture with guards leaves out, with a solver that decides every guard.
expectedGuardLeftOut :: String -> [(EditSymbol Symbol, LeftOut)]
expectedGuardLeftOut name = case name of
    "different leaves" -> [(ReplaceAt $ path at, MixedGuard) | at <- [[0], [0, 0], [1]]]
    "guarded pairs" -> [(ContextAt (path [0]) (fromString "pair") 3 1, ConstrainedHole)]
    _ -> []

-- | g(f(n), n) with a guard on g.
leafGuard :: Guard -> FTA.PlainFTA String Symbol
leafGuard guard = fromRows "s" [("s", [guardedAt "g" ["p", "n"] guard]), ("p", [symbolNode "f" ["n"]]), ("n", numbers)]

-- | The term g(f(2), 1).
leafTerm :: Term Symbol
leafTerm = symbolTerm "g" [symbolTerm "f" [number 2], number 1]

-- | The number below f is above one.
aboveOneAt00 :: Guard
aboveOneAt00 = Satisfies (path [0, 0]) aboveOne

-- | One of the two numbers is above one.
eitherAboveOne :: Guard
eitherAboveOne = Or [Satisfies (path [0, 0]) aboveOne, Satisfies (path [1]) aboveOne]

-- | k(w(v(n))) or k(v(n)), where the number of v(n) at the place of w is above one.
guardedUnwraps :: FTA.PlainFTA String Symbol
guardedUnwraps =
    fromRows
        "s"
        [ ("s", [symbolNode "k" ["c"]])
        , ("c", [symbolNode "w" ["e"], guardedAt "v" ["n"] $ Satisfies (path [0]) aboveOne])
        , ("e", [symbolNode "v" ["n"]])
        , ("n", numbers)
        ]

-- | The term k(w(v(3))).
guardedUnwrapsTerm :: Term Symbol
guardedUnwrapsTerm = symbolTerm "k" [symbolTerm "w" [symbolTerm "v" [number 3]]]

-- | The leaves with the numbers 1, 2, and 3.
numbers :: [FTA.Transition String Symbol Constraint]
numbers = [FTA.Transition (numberSymbol value) [] noConstraint | value <- [1, 2, 3]]

-- | A transition without a constraint, over symbols.
symbolNode :: String -> [String] -> FTA.Transition String Symbol Constraint
symbolNode symbol children = FTA.Transition (fromString symbol) children noConstraint

-- | A transition with a guard, over symbols.
guardedAt :: String -> [String] -> Guard -> FTA.Transition String Symbol Constraint
guardedAt symbol children guard = FTA.Transition (fromString symbol) children $ semanticConstraint guard

-- | A term over symbols from its symbol and children.
symbolTerm :: String -> [Term Symbol] -> Term Symbol
symbolTerm symbol = Term.Node (fromString symbol)

{- | The edits of a fixture with guards, up to one node more than 'bound',
whose edited term has at most 'bound' nodes, with the edited term. The solver
decides the guards.
-}
guardedEdits :: Entailment -> FTA.PlainFTA String Symbol -> Term Symbol -> IO [(Edit Symbol, Term Symbol)]
guardedEdits solver automaton given = do
    result <- either (error . show) id <$> guardedEditAutomaton solver automaton given
    let (plain, decode) = plainSymbols (edits result)
    classes <- either (error . show) id <$> sizedUpTo solver (Size $ bound + 1) plain
    pure
        [ (edit, edited)
        | size <- [1 .. bound + 1]
        , edit <- map decode $ termsOfSize classes (Size size)
        , Just edited <- [applyEdit given edit]
        , toInteger (length edited) <= bound
        ]

-- | Whether the solver decides that a term satisfies a constraint.
decidedBy :: Entailment -> Constraint -> Term Symbol -> IO Bool
decidedBy solver constraint subterm = (== Yes) <$> evaluateConstraint solver constraint subterm

-- | A solver that decides whether the values 1, 2, and 3 are above one.
fullSolver :: Entailment
fullSolver = tableSolver [(1, No), (2, Yes), (3, Yes)]

-- | A solver that decides whether the values 1 and 2 are above one, and not the value 3.
partialSolver :: Entailment
partialSolver = tableSolver [(1, No), (2, Yes)]

{- | A solver from the verdicts of "the value is above one" for some values.
It decides the negation from the same table, because a value refutes the
formula when it does not satisfy it.
-}
tableSolver :: [(Integer, Verdict)] -> Entailment
tableSolver table = Entailment $ \antecedent consequent ->
    pure $ case lookup antecedent [(valueIs value, verdict) | (value, verdict) <- table] of
        Nothing -> Unknown
        Just verdict
            | consequent == aboveOne -> verdict
            | consequent == Formula.Not aboveOne -> negateVerdict verdict
            | otherwise -> Unknown

-- | The refinement that the value is above one.
aboveOne :: Formula
aboveOne = refinementFormula (.> 1)

-- | The refinement that the value is the number.
valueIs :: Integer -> Formula
valueIs value = refinementFormula (.== fromInteger value)

-- | The leaf n with a value.
numberSymbol :: Integer -> Symbol
numberSymbol value = RefinedSymbol (fromString "n") (valueIs value)

-- | The term of a leaf n with a value.
number :: Integer -> Term Symbol
number value = Term.Node (numberSymbol value) []
