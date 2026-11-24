module Data.CFTA.Edit.TreesSpec (spec) where

import Data.Containers.ListUtils (nubOrd)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Test.Hspec (Spec, describe, it, shouldBe)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, noConstraint)
import Data.CFTA.Edit
import qualified Data.CFTA.Edit.Sets as Sets
import Data.CFTA.Edit.Trees
import qualified Data.CFTA.Gen as Gen
import Data.CFTA.Index (ChildIndex (..), Size (..), TransitionIndex (..))
import Data.CFTA.Interned (fromFTA)
import Data.CFTA.Path (path)
import Data.CFTA.Sized (countOfSize, sized, termsOfSize)
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

spec :: Spec
spec = describe "Data.CFTA.Edit.Trees" $ do
    it "gives the edited terms of the definition with their least cost, for one to three edits" $
        mapM_
            ( \(name, automaton, given) ->
                mapM_
                    ( \k -> do
                        let expected = definition k automaton given
                        ((name, k, Map.size expected > 3), found k automaton given) `shouldBe` ((name, k, True), expected)
                    )
                    [1, 2, 3]
            )
            fixtures
    it "has one run for each edit tree, and the generator counts them as the size classes do" $
        mapM_
            ( \(name, automaton, given) ->
                mapM_
                    ( \k -> do
                        let automata = treesOf k automaton given
                            classes = either (error . show) id $ sized automata
                            generator = Gen.fromAutomaton $ fromFTA automata
                            terms = [t | size <- [1 .. bound], t <- termsOfSize classes (Size size)]
                        ((name, k, not (null terms)), [t | t <- terms, runs automata t /= 1]) `shouldBe` ((name, k, True), [])
                        ( (name, k)
                            , and [Gen.countAtSize generator (Size size) == Right (countOfSize classes (Size size)) | size <- [1 .. bound]]
                            )
                            `shouldBe` ((name, k), True)
                    )
                    [1, 2, 3]
            )
            fixtures
    it "has the size classes of the edit sets for one edit" $
        mapM_
            ( \(name, automaton, given) -> do
                let single = either (error . show) id $ sized $ treesOf 1 automaton given
                    sets = either (error . show) id $ sized $ either (error . show) id $ Sets.editSetAutomaton 1 automaton given
                (name, [countOfSize single (Size size) | size <- [1 .. bound]])
                    `shouldBe` (name, [countOfSize sets (Size size) | size <- [1 .. bound]])
            )
            fixtures
    it "is cheaper than any edit set for a wrap with a change inside" $ do
        -- neg around the sum, and two instead of one inside: a wrap and a replacement of the number, 3 nodes.
        let given = Term.Node "add" [lit "one", lit "two"]
            edited = Term.Node "neg" [Term.Node "add" [lit "two", lit "two"]]
            cheapest automaton = minimum [size | (size, result) <- applied automaton, result == edited]
            applied automaton = [(size, result) | (size, term') <- termsUpTo automaton, Just result <- [term']]
            termsUpTo automaton =
                [ (size, applyEditTree given t)
                | size <- [1 .. 8]
                , t <- termsOfSize (either (error . show) id $ sized automaton) (Size size)
                ]
            setsApplied =
                [ (size, Sets.applyEditSet given t)
                | size <- [1 .. 8]
                , t <- termsOfSize (either (error . show) id $ sized $ setsOf 3 expressions given) (Size size)
                ]
        cheapest (treesOf 3 expressions given) `shouldBe` 3
        minimum [size | (size, Just result) <- setsApplied, result == edited] `shouldBe` 7
        -- The tree of 3 nodes: a wrap of the whole term, and a replacement inside it.
        [ editsOfTree t
          | t <- termsOfSize (either (error . show) id $ sized $ treesOf 3 expressions given) (Size 3)
          , applyEditTree given t == Just edited
          ]
            `shouldBe` [ Just
                            [ Term.Node (WrapAt (path []) "neg" (TransitionIndex 1) (ChildIndex 0)) []
                            , Term.Node (ReplaceAt (path [0, 0])) [Term.Node (Material "two") []]
                            ]
                       ]
    it "is cheaper than any edit set for a context wrap with a change inside" $ do
        -- Wrap the sum in add(one, neg(hole)), and put one instead of two inside the sum.
        let given = Term.Node "add" [lit "one", lit "two"]
            edited = Term.Node "add" [lit "one", Term.Node "neg" [Term.Node "add" [lit "one", lit "one"]]]
            cheapest classes apply = minimum [size | size <- [1 .. 12], t <- termsOfSize classes (Size size), apply t == Just edited]
            treeClasses = either (error . show) id $ sized $ treesOf 2 expressions given
            setClasses = either (error . show) id $ sized $ setsOf 2 expressions given
        (cheapest treeClasses (applyEditTree given), cheapest setClasses (Sets.applyEditSet given)) `shouldBe` (6, 7)
    it "allows an unwrap after a wrap at one position, and it can be the cheapest" $ do
        let given = Term.Node "add" [lit "one", Term.Node "neg" [lit "two"]]
            edited = Term.Node "add" [lit "two", lit "one"]
            classes = either (error . show) id $ sized $ treesOf 2 expressions given
        [ (size, editsOfTree t)
          | size <- [1 .. 5]
          , t <- termsOfSize classes (Size size)
          , applyEditTree given t == Just edited
          ]
            `shouldBe` [
                           ( 4
                           , Just
                                [ Term.Node (WrapAt (path []) "add" (TransitionIndex 2) (ChildIndex 1)) [material' "lit" [material' "two" []]]
                                , Term.Node (UnwrapAt (path []) (ChildIndex 0)) []
                                ]
                           )
                       ,
                           ( 5
                           , Just
                                [ Term.Node (ReplaceAt $ path [0, 0]) [material' "two" []]
                                , Term.Node (ReplaceAt $ path [1]) [material' "lit" [material' "one" []]]
                                ]
                           )
                       ]
    it "has one tree for a stack of wraps: the context wrap, and no wrap after a treeable wrap at its index" $ do
        let given = lit "one"
            edited = Term.Node "neg" [Term.Node "neg" [lit "one"]]
            classes = either (error . show) id $ sized $ treesOf 2 expressions given
            twoEdits = [t | t <- termsOfSize classes (Size 2), applyEditTree given t == Just edited]
            sitesOfTree t = fromMaybe [] (editsOfTree t)
        -- The two wraps of neg are the context wrap neg(neg(hole)): one tree.
        map (map (\(Term.Node site _) -> site) . sitesOfTree) twoEdits
            `shouldBe` [[ContextAt (path []) "neg" (TransitionIndex 1) (ChildIndex 0)]]
        -- No wrap or context wrap directly after a wrap or a context wrap at the same position, and no replacement after a wrap.
        mapM_
            ( \(name, automaton, term') -> do
                let all' = either (error . show) id $ sized $ treesOf 3 automaton term'
                    wrapPath symbol = case symbol of
                        WrapAt at _ _ _ -> Just at
                        ContextAt at _ _ _ -> Just at
                        _ -> Nothing
                    replacePath symbol = case symbol of
                        ReplaceAt at -> Just at
                        _ -> Nothing
                    bad =
                        [ (first', second')
                        | size <- [1 .. bound]
                        , t <- termsOfSize all' (Size size)
                        , let edits = sitesOfTree t
                        , (first'@(Term.Node a _), second'@(Term.Node b _)) <- zip edits (drop 1 edits)
                        , Just at <- [wrapPath a]
                        , Just at == wrapPath b || Just at == replacePath b
                        ]
                (name, bad) `shouldBe` (name, [])
            )
            fixtures
    it "counts the trees of each fixture without the stacks of wraps" $
        -- Before the canonical form: 905 and 1547 trees for the expressions (k = 2, 3), 713 and 953 for the binary trees,
        -- 89 and 90 for the statements, and 108 and 238 for the chain, with the sizes up to the bound.
        [ ( name
          , k
          , length
                [t | size <- [1 .. bound], t <- termsOfSize (either (error . show) id $ sized $ treesOf k automaton given) (Size size)]
          )
        | (name, automaton, given) <- fixtures
        , k <- [2, 3]
        ]
            `shouldBe` [ ("expressions", 2, 705)
                       , ("expressions", 3, 891)
                       , ("binary trees over a and b", 2, 633)
                       , ("binary trees over a and b", 3, 745)
                       , ("statements", 2, 83)
                       , ("statements", 3, 83)
                       , ("a chain", 2, 78)
                       , ("a chain", 3, 95)
                       ]

-- | New material from its symbol and children.
material' :: String -> [Term (EditSymbol String)] -> Term (EditSymbol String)
material' = Term.Node . Material

-- | The largest size of an edit tree that the tests compare.
bound :: Integer
bound = 5

treesOf ::
    Int -> FTA.PlainFTA String String -> Term String -> FTA.PlainFTA (TreeState String String) (TreeSymbol String)
treesOf k automaton given = either (error . show) id $ editTreeAutomaton k automaton given

setsOf ::
    Int -> FTA.PlainFTA String String -> Term String -> FTA.PlainFTA (Sets.SetState String String) (Sets.SetSymbol String)
setsOf k automaton given = either (error . show) id $ Sets.editSetAutomaton k automaton given

-- | The edited terms of the trees up to the bound, with their least size.
found :: Int -> FTA.PlainFTA String String -> Term String -> Map.Map (Term String) Int
found k automaton given =
    Map.fromListWith
        min
        [ (result, fromInteger size)
        | size <- [1 .. bound]
        , t <- termsOfSize classes (Size size)
        , Just result <- [applyEditTree given t]
        , result /= given
        ]
  where
    classes = either (error . show) id $ sized $ treesOf k automaton given

data Result = Result
    { rTerm :: Term String
    , rEdits :: Int
    , rCost :: Int
    }

{- | The edited terms by the definition of an edit tree, with their least cost (edits plus new material).

At a position there are no edits, edits below, a replacement by another term of
the state, an unwrap, or a wrap or a context wrap. A wrap holds the old subterm,
or, when the hole has the state of the position, an edit tree of it that has an
edit below or an unwrap at the position, but no replacement and no wrap at the
position: two stacked wraps are one context wrap.
-}
definition :: Int -> FTA.PlainFTA String String -> Term String -> Map.Map (Term String) Int
definition k automaton given =
    Map.fromListWith min [(rTerm r, rCost r) | r <- edit [] k, rEdits r >= 1, rTerm r /= given]
  where
    limit = fromInteger bound
    kept results = [r | r <- results, rCost r <= limit]
    oldAt at = fromMaybe (error "no subterm") $ subtermAt given at
    -- Any edits at a position or below, up to a number, including none.
    edit at j = kept $ unchanged at j <> replacements at j <> unwraps at j <> wraps at j
    -- No replacement at the position, and edits.
    inside at j = kept $ [r | r <- unchanged at j, rEdits r >= 1] <> unwraps at j
    unchanged at j = case oldAt at of
        Term.Node symbol children ->
            [ Result (Term.Node symbol (map rTerm chosen)) (sum (map rEdits chosen)) (sum (map rCost chosen))
            | chosen <- budgeted [edit (at <> [index]) j | index <- [0 .. length children - 1]] j
            ]
    budgeted [] _ = [[]]
    budgeted (options : rest) left = [r : more | r <- options, rEdits r <= left, more <- budgeted rest (left - rEdits r)]
    replacements at j =
        [ Result new 1 (1 + length new)
        | j >= 1
        , new <- termsOf (runState at) (limit - 1)
        , new /= oldAt at
        ]
    unwraps at j =
        [ Result child 1 1
        | j >= 1
        , Term.Node _ children <- [oldAt at]
        , child <- children
        , acceptsAt (runState at) child
        ]
    -- The old subterm in a hole, or an edit tree of it when the hole has the state of the position.
    held at j holeState = Result (oldAt at) 0 0 : [r | holeState == runState at, r <- inside at (j - 1)]
    wraps at j =
        concat
            [ [ Result
                    (Term.Node symbol (before <> (rTerm inner : after)))
                    (1 + rEdits inner)
                    (1 + sum (map length siblings') + rCost inner)
              | siblings' <- siblingTerms others
              , let (before, after) = splitAt hole siblings'
              , inner <- held at j child
              ]
            | j >= 1
            , let state = runState at
            , FTA.Transition symbol children _ <- FTA.transitionsFrom automaton state
            , (hole, child) <- zip [0 ..] children
            , acceptsAt child (oldAt at)
            , let others = [sibling | (other, sibling) <- zip [0 :: Int ..] children, other /= hole]
            ]
            <> [ Result (fill (rTerm inner) context) (1 + rEdits inner) (nodes + rCost inner)
               | j >= 1
               , (context, holeState, nodes, depth) <- holedTerms (runState at) limit
               , depth >= (2 :: Int)
               , acceptsAt holeState (oldAt at)
               , inner <- held at j holeState
               ]
    -- The terms of a state with one placeholder leaf: the state of the placeholder, the nodes besides it, and its depth.
    holedTerms state budget =
        [ (Term.Node symbol (before <> (inner : after)), holeState, 1 + sum (map length siblings') + nodes, depth + 1)
        | budget >= 1
        , FTA.Transition symbol children _ <- FTA.transitionsFrom automaton state
        , (hole, child) <- zip [0 ..] children
        , let others = [sibling | (other, sibling) <- zip [0 :: Int ..] children, other /= hole]
        , siblings' <- siblingTerms others
        , let left = budget - 1 - sum (map length siblings')
        , left >= 0
        , (inner, holeState, nodes, depth) <- (Term.Node "hole" [], child, 0, 0) : holedTerms child left
        , let (before, after) = splitAt hole siblings'
        ]
    fill old (Term.Node "hole" []) = old
    fill old (Term.Node symbol children) = Term.Node symbol (map (fill old) children)
    siblingTerms [] = [[]]
    siblingTerms (state : rest) = [new : others | new <- termsOf state (limit - 1), others <- siblingTerms rest]
    termsOf state size = [candidate | candidate <- allTerms automaton =<< [1 .. size], acceptsAt state candidate]
    runState at = case [ state
                       | state <- FTA.states automaton
                       , acceptsAt state (oldAt at)
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
    ,
        ( "statements"
        , statements
        , Term.Node
            "block"
            [ Term.Node
                "cons"
                [ Term.Node "skip" []
                , Term.Node "cons" [Term.Node "if" [Term.Node "cons" [Term.Node "skip" [], Term.Node "nil" []]], Term.Node "nil" []]
                ]
            ]
        )
    , ("a chain", fromRows "s" [("s", [leaf "a", node "f" ["s"]])], Term.Node "f" [Term.Node "f" [Term.Node "a" []]])
    ]

-- | Blocks of statements: a body is a non-empty list, and an if has a body.
statements :: FTA.PlainFTA String String
statements =
    fromRows
        "m"
        [ ("m", [node "block" ["b"]])
        , ("b", [node "cons" ["s", "l"]])
        , ("l", [leaf "nil", node "cons" ["s", "l"]])
        , ("s", [leaf "skip", node "if" ["b"]])
        ]

trees :: FTA.PlainFTA String String
trees = fromRows "s" [("s", [leaf "a", leaf "b", node "g" ["s", "s"]])]

-- | Expressions: a literal of a number, a negation, or a sum.
expressions :: FTA.PlainFTA String String
expressions = fromRows "e" [("e", [node "lit" ["n"], node "neg" ["e"], node "add" ["e", "e"]]), ("n", [leaf "one", leaf "two"])]

lit :: String -> Term String
lit number = Term.Node "lit" [Term.Node number []]

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

subtermAt :: Term String -> [Int] -> Maybe (Term String)
subtermAt found' [] = Just found'
subtermAt (Term.Node _ children) (index : rest) = case drop index children of
    child : _ -> subtermAt child rest
    [] -> Nothing

replaceAt :: Term String -> [Int] -> Term String -> Maybe (Term String)
replaceAt _ [] new = Just new
replaceAt (Term.Node symbol children) (index : rest) new = case splitAt index children of
    (before, child : after) -> (\changed -> Term.Node symbol (before <> (changed : after))) <$> replaceAt child rest new
    _ -> Nothing

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

fromRows :: String -> [(String, [FTA.Transition String String Constraint])] -> FTA.PlainFTA String String
fromRows initial rows = either (error . show) id $ FTA.mkFTA initial rows

leaf :: String -> FTA.Transition String String Constraint
leaf symbol = FTA.Transition symbol [] noConstraint

node :: String -> [String] -> FTA.Transition String String Constraint
node symbol children = FTA.Transition symbol children noConstraint
