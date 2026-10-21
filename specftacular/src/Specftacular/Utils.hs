{-# LANGUAGE OverloadedStrings #-}

module Specftacular.Utils where

import Data.CFTA.Equality (
    Edge (Edge),
    Node (Node),
    Path,
    createMu,
    equalityConstraint,
    getPath,
    mapNodes,
    mkEdge,
    mkEqConstraints,
    path,
    pathsMatching,
    union,
 )
import Data.CFTA.Symbol (Symbol (Symbol))
import Data.Containers.ListUtils (nubOrd)
import Data.Text (Text)
import Specftacular.Types (TypeSkeleton (..))

-- | The marker that is the first child of a function type.
theArrowNode :: Node Symbol
theArrowNode = Node [Edge "(->)" []]

-- | The node of a function type.
arrowType :: Node Symbol -> Node Symbol -> Node Symbol
arrowType n1 n2 = Node [Edge "->" [theArrowNode, n1, n2]]

-- | The node of a type constructor with its arguments.
mkDatatype :: Text -> [Node Symbol] -> Node Symbol
mkDatatype s ns = Node [Edge (Symbol s) ns]

-- | The leaves of the type variables.
var1, var2, var3, var4, varAcc :: Node Symbol
var1 = Node [Edge "var1" []]
var2 = Node [Edge "var2" []]
var3 = Node [Edge "var3" []]
var4 = Node [Edge "var4" []]
varAcc = Node [Edge "acc" []]

-- | Keep the terms of a node whose type child equals the type.
filterType :: Node Symbol -> Node Symbol -> Node Symbol
filterType n t =
    Node [mkEdge "filter" [t, n] (equalityConstraint $ mkEqConstraints [[path [0], path [1, 0]]])]

{- | The nodes of the terms with k leaves: the atoms, or the applications of
the terms of i leaves to the terms of k - i leaves.
-}
tk :: Node Symbol -> Int -> [Node Symbol]
tk _ 0 = []
tk anyArg 1 = [anyArg]
tk anyArg k = map constructApp [1 .. (k - 1)]
  where
    constructApp :: Int -> Node Symbol
    constructApp i =
        mapp
            (union $ tk anyArg i)
            (union $ tk anyArg (k - i))

{- | The nodes of the terms with k leaves, one node for each shape: the atoms,
or the applications of a shape with i leaves to a shape with k - i leaves,
down to the given depth of applications; below it, a part is the union of
'tk'. Their union is the union of 'tk', and no two of them share a term.
-}
spineParts :: Int -> Node Symbol -> Int -> [Node Symbol]
spineParts _ _ 0 = []
spineParts _ anyArg 1 = [anyArg]
spineParts depth anyArg k
    | depth <= 0 = [union $ tk anyArg k]
    | otherwise =
        [ mapp function argument
        | i <- [1 .. k - 1]
        , function <- spineParts (depth - 1) anyArg i
        , argument <- spineParts (depth - 1) anyArg (k - i)
        ]

mapp :: Node Symbol -> Node Symbol -> Node Symbol
mapp n1 n2 =
    Node
        [ mkEdge
            "app"
            [getPath (path [0, 2]) n1, theArrowNode, n1, n2]
            ( equalityConstraint $
                mkEqConstraints
                    [ [path [1], path [2, 0, 0]] -- it's a function
                    , [path [3, 0], path [2, 0, 1]]
                    , [path [0], path [2, 0, 2]]
                    ]
            )
        ]

allConstructors :: Comps -> [(Text, Int)]
allConstructors comps = nubOrd (concatMap (getConstructors . snd) comps)
  where
    getConstructors :: TypeSkeleton -> [(Text, Int)]
    getConstructors (TVar _) = []
    getConstructors (TFun t1 t2) = getConstructors t1 ++ getConstructors t2
    getConstructors (TCons nm ts) =
        (nm, length ts) : concatMap getConstructors ts

type Comps = [(Text, TypeSkeleton)]

{- | The types that a type variable of the grammar can take. With a depth D,
only the types with at most D levels of constructors and arrows above the
constants and the type variables. Without a depth, all the types ('mtau').
-}
mtauWithin :: Maybe Int -> Comps -> Node Symbol
mtauWithin Nothing comps = mtau comps
mtauWithin (Just depth) comps = go depth
  where
    go 0 = union (globalTyVars ++ [Node [Edge (Symbol nm) []] | (nm, 0) <- allConstructors comps])
    go d =
        let n = go (d - 1)
         in union
                ((arrowType n n : globalTyVars) ++ [Node [Edge (Symbol nm) (replicate arity n)] | (nm, arity) <- allConstructors comps])

mtau :: Comps -> Node Symbol
mtau comps =
    createMu
        ( \n ->
            union
                ( (arrowType n n : globalTyVars)
                    ++ map (Node . (: []) . constructorToEdge n) usedConstructors
                )
        )
  where
    constructorToEdge :: Node Symbol -> (Text, Int) -> Edge Symbol
    constructorToEdge n (nm, arity) = Edge (Symbol nm) (replicate arity n)

    usedConstructors = allConstructors comps

globalTyVars :: [Node Symbol]
globalTyVars = [var1, var2, var3, var4, varAcc]

generalize :: Maybe Int -> Comps -> Node Symbol -> Node Symbol
generalize typeDepth comps n@(Node [_]) =
    Node
        [mkEdge s ns' (equalityConstraint $ mkEqConstraints $ map pathsForVar vars)]
  where
    vars = globalTyVars
    nWithVarsRemoved =
        mapNodes
            ( \x ->
                if x `elem` vars
                    then mtauWithin typeDepth comps
                    else x
            )
            n
    (Node [Edge s ns']) = nWithVarsRemoved

    pathsForVar :: Node Symbol -> [Path]
    pathsForVar v = pathsMatching (== v) n
generalize _ _ n = n -- error $ "cannot generalize: " ++ show n

typeToFta :: TypeSkeleton -> Node Symbol
typeToFta (TVar "a") = var1
typeToFta (TVar "b") = var2
typeToFta (TVar "c") = var3
typeToFta (TVar "d") = var4
typeToFta (TVar "acc") = varAcc
-- TODO: lift this restriction
typeToFta (TVar v) =
    error $
        "Current implementation only supports function signatures with type variables a, b, c, d, and acc, but got "
            ++ show v
typeToFta (TFun t1 t2) = arrowType (typeToFta t1) (typeToFta t2)
typeToFta (TCons "Fun" [t1, t2]) = arrowType (typeToFta t1) (typeToFta t2)
typeToFta (TCons s ts) = mkDatatype s (map typeToFta ts)
