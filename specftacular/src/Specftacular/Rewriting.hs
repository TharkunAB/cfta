{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}

{- | Ordered rewriting with the laws that the search found, and the prover
that completes the rules. A law gives rules: its two sides as templates,
in which the variables of the law are template variables. A rule
rewrites a term only when the term gets smaller in the term order of the
rules, as in Twee. The order is the Knuth-Bendix order, or a lexicographic
path order with a precedence of the function symbols ('TermOrder').
-}
module Specftacular.Rewriting (
    TermOrder (..),
    Rules,
    emptyRules,
    rulesOrder,
    termCompare,
    reducible,
    pruningTemplates,
    joinable,
    kboCompare,
    addLaw,
    addLawRules,
    generalizeLaw,
) where

import Control.Applicative ((<|>))
import Control.Concurrent (forkIO, killThread)
import Control.Concurrent.MVar (newEmptyMVar, putMVar, takeMVar)
import Control.Exception (SomeException, evaluate, mask, onException, throwIO, try)
import Control.Monad (foldM, guard)
import Data.CFTA.Symbol (Symbol (Symbol))
import Data.CFTA.Template (Template (..))
import Data.Containers.ListUtils (nubOrd)
import qualified Data.HashMap.Strict as HashMap
import Data.List (elemIndex, permutations, sortOn)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, isJust, isNothing)
import Data.Ord (Down (..))
import qualified Data.Text as T
import System.IO.Unsafe (unsafePerformIO)
import System.Mem (getAllocationCounter, setAllocationCounter)

import Specftacular.Types

{- | Rules by the head of their left sides (see 'spineHead'), and by the
program shape of their left sides (see 'Shapes'). A rule whose head is a
template variable has the key Nothing, because it can match a term with any
head.
-}
data Index = Index
    { byHead :: !(Map (Maybe (Symbol, Int)) [(Term, Term)])
    -- ^ The rules of each head, the newest first.
    , shapes :: !Shapes
    -- ^ The rules by the program shapes of their left sides.
    , added :: !Int
    -- ^ The number of rules, which orders the rules of 'candidates'.
    }

{- | A trie of the program shapes of the left sides of rules, in preorder:
an application, a symbol, or a template variable. A template variable
matches any annotated subterm. The type annotations are not part of a
shape. A rule is at the end of its shape, with the place that it has in
the order of 'candidates'.
-}
data Shapes = Shapes
    { shapeRules :: ![((Bool, Int), (Term, Term))]
    , shapeApp :: !(Maybe Shapes)
    , shapeSymbols :: !(Map Symbol Shapes)
    , shapeVariable :: !(Maybe Shapes)
    }

-- | One step of a shape: an application, a symbol, or a template variable.
data ShapeStep = AppStep | SymbolStep !Symbol | VariableStep

-- | An index without rules.
emptyIndex :: Index
emptyIndex = Index Map.empty emptyShapes 0

-- | A trie without shapes.
emptyShapes :: Shapes
emptyShapes = Shapes [] Nothing Map.empty Nothing

{- | The shape of a left side in preorder, as 'matchesShape' reads it.
'Nothing' for a term that 'matchesShape' does not accept as a template.
-}
shapeOf :: Term -> Maybe [ShapeStep]
shapeOf (Term h [_]) | isTemplateVar h = Just [VariableStep]
shapeOf (Term "app" [_, f, v]) = (\fs vs -> AppStep : fs ++ vs) <$> shapeOf f <*> shapeOf v
shapeOf (Term a [_]) = Just [SymbolStep a]
shapeOf _ = Nothing

-- | Add a rule at the end of its shape.
insertShape :: [ShapeStep] -> ((Bool, Int), (Term, Term)) -> Shapes -> Shapes
insertShape [] rule node = node{shapeRules = rule : shapeRules node}
insertShape (step : rest) rule node = case step of
    AppStep -> node{shapeApp = Just (insertShape rest rule (fromMaybe emptyShapes (shapeApp node)))}
    SymbolStep a -> node{shapeSymbols = Map.alter (Just . insertShape rest rule . fromMaybe emptyShapes) a (shapeSymbols node)}
    VariableStep -> node{shapeVariable = Just (insertShape rest rule (fromMaybe emptyShapes (shapeVariable node)))}

{- | The rules whose left sides have the shape of a term, as 'matchesShape'
decides it, with their places in the order of 'candidates'.
-}
lookupShapes :: Shapes -> Term -> [((Bool, Int), (Term, Term))]
lookupShapes root t = go root [t]
  where
    go node [] = shapeRules node
    go node (u : us) = viaVariable ++ viaShape
      where
        viaVariable = case (shapeVariable node, u) of
            (Just next, Term _ (_ : _)) -> go next us
            _ -> []
        viaShape = case u of
            Term "app" [_, f, v] -> maybe [] (\next -> go next (f : v : us)) (shapeApp node)
            Term a [_] -> maybe [] (\next -> go next us) (Map.lookup a (shapeSymbols node))
            _ -> []

{- | The rules of the laws. One-way orientation is independent of type annotations.
Each rewrite checks the order after type instantiation. A rule
rewrites only if each template variable of its right side is in its left
side. The other rules cannot rewrite, because a match of the left side
does not give the right side, but they show that an equation follows
(see 'subsumed').
-}
data Rules = Rules
    { rulesOrder :: !TermOrder
    -- ^ The order that orients the rules and decides each rewrite.
    , oriented :: !Index
    -- ^ The rules with a type-independent orientation.
    , unoriented :: !Index
    -- ^ The rules that make some instances smaller.
    , nonRewriting :: !Index
    -- ^ The rules that cannot rewrite.
    }

-- | No rules, with the order of the rules to come.
emptyRules :: TermOrder -> Rules
emptyRules order = Rules order emptyIndex emptyIndex emptyIndex

{- | The order of the rewriting.

'KnuthBendix' is the Knuth-Bendix order of 'kboCompare' and 'kboGreater':
each symbol and each application has the weight 1. It orients an equation
towards the side with fewer symbols, so a rule never makes a term larger,
and a term that a rule rewrites has a smaller form in the search.

'PathOrder' is the lexicographic path order on the uncurried terms: the
function symbol of the spine of an application with its arguments. The list
gives the precedence of the function symbols from the lowest to the
highest. A symbol that the list does not give is below each listed symbol,
and generated variables are below all function symbols. The order can
make a term larger, for example
@reverse (xs ++ ys) > reverse ys ++ reverse xs@ when @reverse@ is above
@++@. Thus a rule can rewrite a term to a form with more symbols, and the
search can then prune a term whose smaller form is over the size bound.
-}
data TermOrder
    = KnuthBendix
    | PathOrder ![T.Text]
    deriving (Eq, Show)

{- | The total order of ground terms that decides the rewrites of the search
and the order of the terms of a bucket. The generated variables are
constants, below all function symbols.
-}
termCompare :: TermOrder -> (Symbol -> Bool) -> Term -> Term -> Ordering
termCompare KnuthBendix isVar = kboCompare isVar
termCompare (PathOrder precedence) isVar = lpoCompare precedence isVar

-- | Whether a ground term is greater than another in the order.
orderGreater :: TermOrder -> (Symbol -> Bool) -> Term -> Term -> Bool
orderGreater order isVar a b = termCompare order isVar a b == GT

{- | Whether a template is greater than another for each instance in which
the ranked template variables compare as the ranking says (see
'kboGreater').
-}
rankedGreater :: TermOrder -> Map Symbol Int -> Term -> Term -> Bool
rankedGreater KnuthBendix rank = kboGreater rank
rankedGreater (PathOrder precedence) rank = lpoGreater precedence rank

-- | Whether a template is greater than another for each term and type instance.
independentGreater :: TermOrder -> Term -> Term -> Bool
independentGreater KnuthBendix = annotationIndependentGreater
independentGreater (PathOrder precedence) = lpoGreater precedence Map.empty

{- | Whether the decrease of a template also holds when both sides take
more arguments. The path order compares the uncurried terms, so the
arguments join the spines: when @a@ is above @f@, @f a > a@ but
@f a x < a x@. One fresh argument decides each number of arguments: the
heads compare in the same way, and no subterm of the left side contains
the fresh variable. A side whose type is not a function type or a type
variable takes no argument. The Knuth-Bendix order is closed under
contexts.
-}
appliedGreater :: TermOrder -> Map Symbol Int -> Term -> Term -> Bool
appliedGreater KnuthBendix _ _ _ = True
appliedGreater (PathOrder precedence) rank l r = case l of
    Term _ (Term "->" [_, a, b] : _) -> applied a b
    Term _ (Term v [] : _) | isTypeVar v -> applied (Term "<t>applied" []) (Term "<t>applied" [])
    _ -> True
  where
    applied a b = lpoGreater precedence rank (apply a b l) (apply a b r)
    apply a b t = Term "app" [b, t, Term "<v>applied" [a]]

{- | Add the rules of an equation, and give the new rules too. Keep one
orientation only when its decrease is independent of type annotations
and holds when both sides take more arguments. Other equations retain
both directions. Each rewrite still checks its instantiated order.
-}
addEquation :: (Term, Term) -> Rules -> ([(Term, Term)], Rules)
addEquation (l, r) rules
    | decreasing l r = ([(l, r)], rules{oriented = insert (l, r) (oriented rules)})
    | decreasing r l = ([(r, l)], rules{oriented = insert (r, l) (oriented rules)})
    | otherwise = ([(l, r), (r, l)], foldr addUnoriented rules [(l, r), (r, l)])
  where
    decreasing a b = independentGreater (rulesOrder rules) a b && appliedGreater (rulesOrder rules) Map.empty a b
    addUnoriented rule@(a, b) rs
        | all (`elem` templateVars a) (templateVars b) = rs{unoriented = insert rule (unoriented rs)}
        | otherwise = rs{nonRewriting = insert rule (nonRewriting rs)}
    insert rule@(a, _) index =
        Index
            { byHead = Map.insertWith (++) (key a) [rule] (byHead index)
            , shapes =
                maybe (shapes index) (\shape -> insertShape shape ((isNothing (key a), added index), rule) (shapes index)) (shapeOf a)
            , added = added index + 1
            }
    key a = case spineHead a of
        (h, _) | isTemplateVar h -> Nothing
        k -> Just k

-- | All the rules.
allRules :: Rules -> [(Term, Term)]
allRules rules = concatMap (concat . Map.elems . byHead) [oriented rules, unoriented rules, nonRewriting rules]

{- | The head of a term: the symbol of the function of its application
spine, and the number of the arguments of the spine. A template whose
head is a symbol matches only a term with the same head.
-}
spineHead :: Term -> (Symbol, Int)
spineHead (Term "app" [_, f, _]) = fmap (+ 1) (spineHead f)
spineHead (Term s _) = (s, 0)

{- | The rules whose left sides have the program shape of a term (see
'matchesShape'): the rules with the head of the term, the newest first, and
then the rules with a template variable as head, the newest first.
-}
candidates :: Index -> Term -> [(Term, Term)]
candidates index t = map snd (sortOn (\((variableHead, place), _) -> (variableHead, Down place)) (lookupShapes (shapes index) t))

-- | Whether a symbol is a template variable.
isTemplateVar :: Symbol -> Bool
isTemplateVar (Symbol name) = "<v>" `T.isPrefixOf` name

{- | Rewrite one subterm of a term, the outermost and leftmost first. A rule
rewrites a subterm only if the order says that the subterm is greater
than its rewritten form. The subterms are the term, and the function and
the argument of an application; the types are not subterms. The path
order compares a function together with its arguments (see
'appliedGreater'), so there the rewrite of a function must make the
application that contains its arguments smaller.
-}
rewriteStep :: (Term -> Term -> Bool) -> Rules -> Term -> Maybe Term
rewriteStep greater rules = go id
  where
    -- The application of a function to its arguments, for the order check.
    inFunction context ty v = case rulesOrder rules of
        PathOrder _ -> context . (\f' -> Term "app" [ty, f', v])
        KnuthBendix -> id
    go context t =
        case [ r'
             | (l, r) <- candidates (oriented rules) t
             , Just s <- [matchTyped l t Map.empty]
             , Just r' <- [instantiate s r]
             , greater (context t) (context r')
             ]
            ++ [ r'
               | (l, r) <- candidates (unoriented rules) t
               , Just s <- [matchTyped l t Map.empty]
               , Just r' <- [instantiate s r]
               , greater (context t) (context r')
               ] of
            r' : _ -> Just r'
            [] -> case t of
                Term "app" [ty, f, v] ->
                    (\f' -> Term "app" [ty, f', v]) <$> go (inFunction context ty v) f
                        <|> (\v' -> Term "app" [ty, f, v']) <$> go id v
                _ -> Nothing

{- | The normal form of a term: rewrite it until no rule rewrites it. Each
step makes the term smaller in a well-founded order, so this ends.
-}
normalForm :: (Term -> Term -> Bool) -> Rules -> Term -> Term
normalForm greater rules t = maybe t (normalForm greater rules) (rewriteStep greater rules t)

{- | Whether a rule rewrites a subterm of the term to a smaller term in the
Knuth-Bendix order. Then the term equals a smaller term, which the search
sees, so the term is redundant. This is ordered rewriting, as in Twee: a
law that the order cannot orient, such as commutativity, rewrites an
instance only when the instance gets smaller.
-}
reducible :: (Symbol -> Bool) -> Rules -> Term -> Bool
reducible isVar rules = isJust . rewriteStep (orderGreater (rulesOrder rules) isVar) rules

{- | Templates of uniformly decreasing linear rules up to the given size.
The enumeration oracle rejects partial terms that contain these patterns.
A pattern also matches a function, so its rule must decrease also when
both sides take more arguments (see 'appliedGreater').
A pattern can omit type annotations when the original rule matches its
principal type. Other patterns keep exact carrier annotations. Repeated
term variables cannot become independent holes.
-}
pruningTemplates :: Sig -> Int -> Rules -> [Template Symbol]
pruningTemplates sig size rules =
    nubOrd
        [ template
        | (l, r) <- allRules rules
        , let vs = templateVars l
        , length vs == length (nubOrd vs)
        , leaves l <= size
        , Term "app" [_, _, _] <- [l]
        , template <- case principalType sig l of
            Just principal
                | independentGreater (rulesOrder rules) l r
                , appliedGreater (rulesOrder rules) Map.empty l r
                , rewrites l r principal ->
                    [rawTemplate (const Hole) l]
            _ ->
                [ rawTemplate exactType l'
                | Just l' <- [specialize l]
                , rewrites l r l'
                , Just bindings <- [matchTemplate l l' Map.empty]
                , Just r' <- [instantiate bindings r]
                , rankedGreater (rulesOrder rules) Map.empty l' r'
                , appliedGreater (rulesOrder rules) Map.empty l' r'
                ]
        ]
  where
    rewrites l r target = isJust (matchTemplate l target Map.empty >>= (`instantiate` r))
    types = Map.fromList [(Symbol ("<t>" <> name), typeSkeletonToTerm ty) | (ty, name) <- carriers]
    specialize (Term "app" [ty, f, x]) =
        (\ty' f' x' -> Term "app" [ty', f', x']) <$> instantiateType types ty <*> specialize f <*> specialize x
    specialize (Term s [ty]) = (\ty' -> Term s [ty']) <$> instantiateType types ty
    specialize _ = Nothing
    exactType (Term s ts) = TemplateNode s (map exactType ts)
    rawTemplate annotation (Term "app" [ty, f, x]) =
        TemplateNode "app" [annotation ty, TemplateNode "(->)" [], rawTemplate annotation f, rawTemplate annotation x]
    rawTemplate annotation (Term s [ty])
        | isTemplateVar s = case annotation ty of
            Hole -> Hole
            t -> AnyPrefix [t]
        | otherwise = TemplateNode s [annotation ty]
    rawTemplate _ _ = error "pruningTemplates: invalid rule"

{- | Prove a decrease that cannot depend on the type annotations. The
variable conditions of 'kboGreater' preserve the weight comparison under
term substitution. Equal weights need a strict function comparison or a
strict comparison of constant names. Identical functions stay identical
under one shared term and type substitution.
-}
annotationIndependentGreater :: Term -> Term -> Bool
annotationIndependentGreater a b =
    kboGreater Map.empty a b && (weight a > weight b || tie a b)
  where
    tie (Term "app" [_, f, v]) (Term "app" [_, g, u])
        | f == g = tie v u
        | otherwise = annotationIndependentGreater f g
    tie (Term f [_]) (Term g [_])
        | not (isTemplateVar f || isTemplateVar g) = f > g
    tie _ _ = False

{- | Infer the principal annotations of a linear pattern. Each occurrence
of a signature constant gets fresh type variables. Given values keep their
declared types. The rule matcher treats the fresh variables as rigid, so a
match of the rule against this result proves that it covers every instance.
-}
principalType :: Sig -> Term -> Maybe Term
principalType sig term = do
    -- Custom signatures can use arbitrary type symbols. Keep the inference
    -- variables separate from every declared type symbol.
    guard (not (any (reserved . typeSkeletonToTerm . sfTypeRep) (Map.elems sig)))
    (annotated, equations) <- annotate "" term
    substitution <- unify Map.empty equations
    pure (annotations (substitute substitution) annotated)
  where
    fresh path name = Term (Symbol ("<p>" <> path <> ":" <> name)) []
    annotate path (Term "app" [_, f, x]) = do
        (f', fs) <- annotate (path <> "f") f
        (x', xs) <- annotate (path <> "x") x
        let result = fresh path ""
        pure (Term "app" [result, f', x'], (typeOf f', Term "->" [Term "(->)" [], typeOf x', result]) : fs ++ xs)
    annotate path (Term s@(Symbol name) [_])
        | isTemplateVar s = Just (Term s [fresh path ""], [])
        | otherwise = do
            fun <- Map.lookup name sig
            let ty = case fun of
                    GivenFun{} -> typeSkeletonToTerm (sfTypeRep fun)
                    _ -> instanceType path (generalizeType (sfTypeRep fun))
            pure (Term s [ty], [])
    annotate _ _ = Nothing
    instanceType path (TVar name) = fresh path name
    instanceType path (TCons name args) = Term (Symbol name) (map (instanceType path) args)
    instanceType path (TFun a b) = Term "->" [Term "(->)" [], instanceType path a, instanceType path b]
    typeOf (Term _ (ty : _)) = ty
    typeOf _ = error "principalType: missing annotation"
    annotations f (Term "app" [ty, g, x]) = Term "app" [f ty, annotations f g, annotations f x]
    annotations f (Term s [ty]) = Term s [f ty]
    annotations _ t = t
    meta (Symbol name) = "<p>" `T.isPrefixOf` name
    reserved (Term h ts) = meta h || any reserved ts
    substitute s (Term h ts) = case Map.lookup h s of
        Just u | null ts -> substitute s u
        _ -> Term h (map (substitute s) ts)
    occurs h (Term k ts) = h == k || any (occurs h) ts
    unify s [] = Just s
    unify s ((a, b) : rest) = case (substitute s a, substitute s b) of
        (a', b') | a' == b' -> unify s rest
        (Term h [], b') | meta h, not (occurs h b') -> unify (Map.insert h b' s) rest
        (a', Term h []) | meta h, not (occurs h a') -> unify (Map.insert h a' s) rest
        (Term h as, Term k bs) | h == k, length as == length bs -> unify s (zip as bs ++ rest)
        _ -> Nothing

{- | Infer an equation scheme. This function does not test the equation.
Signature constants must meet the existing parametric carrier contract.
Given variables retain their concrete type constructors. Each original
variable has one type skeleton across both sides. Ordinary constants get
fresh instances of their declared type scheme at each occurrence.
-}
regeneraliseEquation :: Sig -> (Term, Term) -> Maybe (Term, Term)
regeneraliseEquation sig (lhs, rhs) = do
    guard
        (not (any reserved (Map.keys sig ++ concatMap typeNames (map sfTypeRep (Map.elems sig)) ++ symbols lhs ++ symbols rhs)))
    (left, leftConstraints) <- annotate "L" lhs
    (right, rightConstraints) <- annotate "R" rhs
    bindings <-
        foldM
            (\s (a, b) -> unifyType a b s)
            Map.empty
            ((typeOf left, typeOf right) : leftConstraints ++ rightConstraints)
    let proposal@(a, b) = (substitute bindings left, substitute bindings right)
    -- One shared match must reconstruct both original annotated terms.
    matched <- matchTemplate a lhs Map.empty
    _ <- matchTemplate b rhs matched
    pure (canonical proposal)
  where
    reserved name = "<t>" `T.isPrefixOf` name || "<v>" `T.isPrefixOf` name
    symbols (Term (Symbol name) children) = name : concatMap symbols children
    typeNames (TVar name) = [name]
    typeNames (TCons name children) = name : concatMap typeNames children
    typeNames (TFun a b) = typeNames a ++ typeNames b
    variableNames (Term "app" [_, f, x]) = variableNames f ++ variableNames x
    variableNames (Term symbol@(Symbol name) [_]) = case Map.lookup name sig of
        Just (GivenFun{given_info = GivenVar{}}) -> [symbol]
        _ -> []
    variableNames _ = []
    variables = Map.fromList (zip (nubOrd (variableNames lhs ++ variableNames rhs)) [0 :: Int ..])
    fresh name = Term (Symbol ("<t>rg:" <> name)) []
    arrow a b = Term "->" [Term "(->)" [], a, b]
    typeOf (Term _ (ty : _)) = ty
    typeOf _ = error "regeneraliseEquation: missing inferred annotation"
    -- Each position of one given type can vary. Repeated uses share it.
    givenType path ty
        | ty `elem` map fst carriers = fresh path
    givenType path (TVar _) = fresh path
    givenType path (TFun a b) = arrow (givenType (path <> ":0") a) (givenType (path <> ":1") b)
    givenType path (TCons name children) =
        Term (Symbol name) [givenType (path <> ":" <> T.pack (show index)) child | (index, child) <- zip [0 :: Int ..] children]
    -- Equal declaration binders stay equal within this constant occurrence.
    declaredType path (TVar name) = fresh ("c:" <> path <> ":" <> name)
    declaredType path (TFun a b) = arrow (declaredType path a) (declaredType path b)
    declaredType path (TCons name children) = Term (Symbol name) (map (declaredType path) children)
    annotate path (Term "app" [_, f, x]) = do
        (f', fs) <- annotate (path <> "f") f
        (x', xs) <- annotate (path <> "x") x
        let result = fresh ("r:" <> path)
        pure (Term "app" [result, f', x'], (typeOf f', arrow (typeOf x') result) : fs ++ xs)
    annotate path (Term symbol@(Symbol name) [oldType]) = do
        fun <- Map.lookup name sig
        case fun of
            GivenFun{given_info = GivenVar{}} -> do
                guard (oldType == typeSkeletonToTerm (sfTypeRep fun))
                index <- Map.lookup symbol variables
                let ty = givenType ("v:" <> T.pack (show index)) (sfTypeRep fun)
                pure (Term (Symbol ("<v>rg:" <> T.pack (show index))) [ty], [])
            GivenFun{} -> do
                guard (oldType == typeSkeletonToTerm (sfTypeRep fun))
                pure (Term symbol [oldType], [])
            _ -> pure (Term symbol [declaredType path (generalizeType (sfTypeRep fun))], [])
    annotate _ _ = Nothing

{- | Validate a more general type scheme before adding its rewrite rules.
Each independent type binder gets a distinct abstract carrier. Each term
variable gets its own generator at the inferred type. Missing instances,
failed inference, and rejected or untestable equations keep the original law.
The result type and the original equality function must remain the same.
The signature constants must meet the parametric carrier contract. With a
sample variable (see 'sigGivens'), the two sides are functions, and the
test applies them to the value of the sample variable.
-}
generalizeLaw ::
    (TypeSkeleton -> Maybe Instance) ->
    [TestCase] ->
    Sig ->
    Maybe (T.Text, Func) ->
    (TypeSkeleton, Value) ->
    Term ->
    IO (Sig, Term)
generalizeLaw resolve cases sig sample (equalityType, equalityValue) original@(Term "(==)" [equality, lhs, rhs]) =
    case prepare of
        Nothing -> pure (sig, original)
        Just (newSig, law, required, eq, left, right) -> do
            valid <- foldM (check required eq left right) True cases
            pure (if valid then (newSig, law) else (sig, original))
  where
    check _ _ _ _ False _ = pure False
    check required eq left right True testcase = do
        let values = testCaseValues (maybe required (\(x, f) -> Map.insert x f required) sample) testcase
            observe value = maybe value (\(x, _) -> apply value (values Map.! x)) sample
        result <- valuesEqual eq (observe (left values)) (observe (right values))
        pure (result == Just True)
    prepare = do
        proposal@(a, b) <- regeneraliseEquation sig (lhs, rhs)
        guard (proposal /= canonical (toTemplate sig lhs, toTemplate sig rhs))
        let typeVars = nubOrd (foldMap variable a ++ foldMap variable b)
            variable symbol = [symbol | isTypeVar symbol]
        guard (length typeVars <= length carriers)
        let types = Map.fromList (zip typeVars (map (typeSkeletonToTerm . fst) carriers))
            vars = templateVarLeaves (substitute types a) ++ templateVarLeaves (substitute types b)
        (required, bindings, _) <- foldM allocate (Map.empty, types, Map.empty) (nubOrd vars)
        let newSig = required `Map.union` sig
            leftTerm = substitute bindings a
            rightTerm = substitute bindings b
        resultType <- either (const Nothing) Just (termType newSig leftTerm)
        rightType <- either (const Nothing) Just (termType newSig rightTerm)
        guard (resultType == rightType)
        guard (resultType == equalityType)
        left <- either (const Nothing) Just (compileTerm newSig leftTerm)
        right <- either (const Nothing) Just (compileTerm newSig rightTerm)
        pure (newSig, Term "(==)" [equality, leftTerm, rightTerm], required, equalityValue, left, right)
    allocate (required, bindings, counts) (Term name [annotation]) = do
        ty <- either (const Nothing) Just (annotationType annotation)
        inst <- resolve ty
        let start = Map.findWithDefault 0 ty counts
            select index =
                let info = GivenVar (inst_prefix inst) (inst_text inst) index (inst_gen inst)
                    label = gvToName info
                    occupied = Map.member label required || Map.member label sig
                 in if occupied then select (index + 1) else (index, label, GivenFun info ty)
            (index, label, fun) = select start
        pure
            ( Map.insert label fun required
            , Map.insert name (Term (Symbol label) [annotation]) bindings
            , Map.insert ty (index + 1) counts
            )
    allocate _ _ = Nothing
generalizeLaw _ _ sig _ _ law = pure (sig, law)

{- | Whether the known laws prove a law: the two sides of the law have the
same normal form, or their normal forms are an instance of a rule (see
'subsumed'). The variables of the law are constants here. Each step is an
instance of a known law, so then the law follows from the known laws for
all values of its variables.
-}
joinable :: (Symbol -> Bool) -> Rules -> Term -> Term -> Bool
joinable isVar rules a b = a' == b' || subsumed rules (a', b') || subsumed rules (b', a')
  where
    a' = normalForm (orderGreater (rulesOrder rules) isVar) rules a
    b' = normalForm (orderGreater (rulesOrder rules) isVar) rules b

{- | Replace term and type variables with their matched instances.
An unmatched variable cannot supply a rewrite result.
-}
instantiate :: Map Symbol Term -> Term -> Maybe Term
instantiate s (Term "app" [ty, f, v]) =
    (\ty' f' v' -> Term "app" [ty', f', v']) <$> instantiateType s ty <*> instantiate s f <*> instantiate s v
instantiate s (Term h [ty])
    | isTemplateVar h = Map.lookup h s
    | otherwise = (\ty' -> Term h [ty']) <$> instantiateType s ty
instantiate _ _ = Nothing

-- | Whether a symbol is a type variable in a rule.
isTypeVar :: Symbol -> Bool
isTypeVar (Symbol name) = "<t>" `T.isPrefixOf` name

-- | Apply the type substitution once. Its results belong to the target term.
instantiateType :: Map Symbol Term -> Term -> Maybe Term
instantiateType _ t | not (hasTypeVars t) = Just t
instantiateType s (Term h []) | isTypeVar h = Map.lookup h s
instantiateType s (Term h ts) = Term h <$> traverse (instantiateType s) ts

-- | Match a type with one consistent substitution for all its variables.
matchTypeTerm :: Term -> Term -> Map Symbol Term -> Maybe (Map Symbol Term)
matchTypeTerm p t s | p == t && not (hasTypeVars p) = Just s
matchTypeTerm (Term h []) t s
    | isTypeVar h = bindMatch h t s
matchTypeTerm (Term h ts) (Term k us) s
    | h == k = matchChildren ts us s
  where
    matchChildren [] [] m = Just m
    matchChildren (a : as) (b : bs) m = matchTypeTerm a b m >>= matchChildren as bs
    matchChildren _ _ _ = Nothing
matchTypeTerm _ _ _ = Nothing

{- | Whether a type contains a rule type variable. Matching treats the
variables of its target as rigid. Its substitution applies only once.
-}
hasTypeVars :: Term -> Bool
hasTypeVars = any isTypeVar

-- | Bind one pattern variable, or check its previous occurrence.
bindMatch :: Symbol -> Term -> Map Symbol Term -> Maybe (Map Symbol Term)
bindMatch h t s = case Map.lookup h s of
    Nothing -> Just (Map.insert h t s)
    Just u | u == t -> Just s
    _ -> Nothing

{- | Match term and type variables together. A repeated variable must
have the same term or type at each occurrence.
-}
matchTemplate :: Term -> Term -> Map Symbol Term -> Maybe (Map Symbol Term)
matchTemplate pat target bindings = do
    guard (matchesShape pat target)
    matchTyped pat target bindings

{- | Check the program symbols and application structure before its types.
Template variables accept any annotated subtree. This check does not bind
variables or inspect annotations. A successful typed match passes it.
-}
matchesShape :: Term -> Term -> Bool
matchesShape (Term h [_]) (Term _ (_ : _)) | isTemplateVar h = True
matchesShape (Term "app" [_, f, v]) (Term "app" [_, f', v']) =
    matchesShape f f' && matchesShape v v'
matchesShape (Term a [_]) (Term b [_]) = a == b
matchesShape _ _ = False

-- | Match all annotations and repeated bindings after the shape check.
matchTyped :: Term -> Term -> Map Symbol Term -> Maybe (Map Symbol Term)
matchTyped (Term h [ty]) t s
    | isTemplateVar h = case t of
        Term _ (ty' : _) -> matchTypeTerm ty ty' s >>= bindMatch h t
        _ -> Nothing
matchTyped (Term "app" [ty, f, v]) (Term "app" [ty', f', v']) s =
    matchTypeTerm ty ty' s >>= matchTyped f f' >>= matchTyped v v'
matchTyped (Term a [ty]) (Term b [ty']) s
    | a == b = matchTypeTerm ty ty' s
matchTyped _ _ _ = Nothing

{- | The weight of a term in the Knuth-Bendix order: each symbol has the
weight 1, and an application is the binary symbol app.
-}
weight :: Term -> Int
weight (Term "app" [_, f, v]) = 1 + weight f + weight v
weight _ = 1

{- | The number of leaves of a term, which is the size of a term in the
search.
-}
leaves :: Term -> Int
leaves (Term "app" [_, f, v]) = leaves f + leaves v
leaves _ = 1

{- | The Knuth-Bendix order on ground terms. Each symbol has the weight 1.
An application is the binary symbol app, which is above the other
symbols. Of the other symbols, the generated variables are below the
constants, so that the more general terms come first, and symbols of one
kind compare by their names, then by their types. The generated
variables of a term are constants here. Smaller type instances come first.
The order is total,
well-founded, and closed under contexts, so rewriting with it ends.
-}
kboCompare :: (Symbol -> Bool) -> Term -> Term -> Ordering
kboCompare isVar s t = compare (weight s) (weight t) <> sameWeight s t
  where
    sameWeight (Term "app" [_, f, v]) (Term "app" [_, g, u]) =
        kboCompare isVar f g <> kboCompare isVar v u
    sameWeight (Term "app" _) _ = GT
    sameWeight _ (Term "app" _) = LT
    sameWeight (Term a tys) (Term b tys') =
        compare (not (isVar a)) (not (isVar b)) <> compare a b <> typeOrder tys tys'

-- | Prefer smaller type instances before comparing their names.
typeOrder :: [Term] -> [Term] -> Ordering
typeOrder as bs = compare (rank as) (rank bs)
  where
    rank ts = (sum (map nodes ts), sum (map concrete ts), ts)
    nodes (Term _ ts) = 1 + sum (map nodes ts) :: Int
    concrete t@(Term h [])
        | isTypeVar h || h == "(->)" || t `elem` map (typeSkeletonToTerm . fst) carriers = 0
        | otherwise = 1 :: Int
    concrete (Term _ ts) = sum (map concrete ts)

{- | The Knuth-Bendix order on templates: whether s > t for each instance in
which the template variables compare as the ranking says. A template
variable without a rank compares with no other term, and a template
variable is never greater than a constant or below it. Other symbols
compare as in 'kboCompare'.

The instance of s must not be lighter than the instance of t. Let c x be
the number of occurrences of x in s minus the number in t. A variable
without a rank can have any weight, so c x must not be negative. For
the ranked variables, a greater variable has an instance that is not
lighter, so the sum of c over the variables of a rank and the greater
ranks must not be negative, for each rank.
-}
kboGreater :: Map Symbol Int -> Term -> Term -> Bool
kboGreater rank s t =
    ws >= wt
        && all ((>= 0) . c) unranked
        && and [sum [c x | (x, j) <- ranked, j >= i] >= 0 | (_, i) <- ranked]
        && (ws > wt || sameWeight s t)
  where
    ws = weight s
    wt = weight t
    -- The occurrences of the variables of s, minus those of t. A term has
    -- few variables, so a list is enough.
    diff = occurrences (-1) t (occurrences 1 s [])
    occurrences n (Term "app" [_, f, v]) m = occurrences n v (occurrences n f m)
    occurrences n (Term x _) m
        | isTemplateVar x = add x n m
        | otherwise = m
    add x n ((y, k) : rest)
        | x == y = (y, k + n) : rest
        | otherwise = (y, k) : add x n rest
    add x n [] = [(x, n)]
    -- The ranked variables with their ranks. Each rank needs the sum of c
    -- over its variables and the variables of the greater ranks.
    ranked = [(x, i) | (x, _) <- diff, Just i <- [Map.lookup x rank]]
    unranked = [x | (x, _) <- diff, x `Map.notMember` rank]
    c x = fromMaybe 0 (lookup x diff)
    -- With equal functions, the arguments have equal weights and the same
    -- occurrences of the variables as s and t, so only their order is left
    -- to compare.
    sameWeight (Term "app" [_, f, v]) (Term "app" [_, g, u])
        | f == g = sameWeight v u
        | otherwise = kboGreater rank f g
    sameWeight (Term a tys@[_]) (Term b tys'@[_])
        | isTemplateVar a || isTemplateVar b =
            case (Map.lookup a rank, Map.lookup b rank) of
                (Just i, Just j) -> i > j
                _ -> False
        | otherwise = (compare a b <> typeOrder tys tys') == GT
    sameWeight _ _ = False

{- | The template variables of a template, from left to right, with each
occurrence.
-}
templateVars :: Term -> [Symbol]
templateVars (Term "app" [_, f, v]) = templateVars f ++ templateVars v
templateVars (Term x _) = [x | isTemplateVar x]

{- | The leaves of a template that are template variables, from left to
right, once each.
-}
templateVarLeaves :: Term -> [Term]
templateVarLeaves t = nubOrd (go t)
  where
    go (Term "app" [_, f, v]) = go f ++ go v
    go u@(Term x _) = [u | isTemplateVar x]

-- | Give separate names to the term and type variables of a template.
rename :: (Symbol -> Symbol) -> (Symbol -> Symbol) -> Term -> Term
rename termName typeName = go
  where
    go (Term "app" [ty, f, v]) = Term "app" [types ty, go f, go v]
    go (Term h tys) = Term (if isTemplateVar h then termName h else h) (map types tys)
    types (Term h ts) = Term (if null ts && isTypeVar h then typeName h else h) (map types ts)

{- | Apply a unification substitution through term and type variables.
Unlike matching, unification can bind a variable to another flexible
variable. Follow these bindings transitively. Both occurs checks prevent
cycles. Ground-order variable merges contain no type bindings.
-}
substitute :: Map Symbol Term -> Term -> Term
substitute s (Term "app" [ty, f, v]) =
    Term "app" [substituteType s ty, substitute s f, substitute s v]
substitute s (Term h [ty])
    | isTemplateVar h, Just u <- Map.lookup h s = substitute s u
    | otherwise = Term h [substituteType s ty]
substitute _ t = t

-- | Apply the type part of a unification substitution transitively.
substituteType :: Map Symbol Term -> Term -> Term
substituteType s (Term h [])
    | isTypeVar h, Just ty <- Map.lookup h s = substituteType s ty
substituteType s (Term h ts) = Term h (map (substituteType s) ts)

{- | Unify two templates and their annotations. Term variables bind only
to terms. Type variables bind only to types. The two namespaces have
distinct prefixes. Each binding preserves the annotation constraints and
passes the occurs check of its namespace.
-}
unify :: Term -> Term -> Maybe (Map Symbol Term)
unify a0 b0 = go a0 b0 Map.empty
  where
    go a b s = case (walk s a, walk s b) of
        (Term x [ty], t) | isTemplateVar x -> bind s x ty t
        (t, Term x [ty]) | isTemplateVar x -> bind s x ty t
        (Term "app" [ty, f, v], Term "app" [ty', g, u]) ->
            unifyType ty ty' s >>= go f g >>= go v u
        (Term c [ty], Term d [ty']) | c == d -> unifyType ty ty' s
        _ -> Nothing
    walk s t@(Term x [_])
        | isTemplateVar x, Just u <- Map.lookup x s = walk s u
        | otherwise = t
    walk _ t = t
    bind s x ty t = case t of
        Term y [ty'] | y == x -> unifyType ty ty' s
        Term _ (ty' : _) -> do
            s' <- unifyType ty ty' s
            guard (not (occurs s' x t))
            Just (Map.insert x t s')
        _ -> Nothing
    occurs s x u = case walk s u of
        Term "app" [_, f, v] -> occurs s x f || occurs s x v
        Term y _ -> y == x

-- | Unify types structurally. Reject infinite types and different constructors.
unifyType :: Term -> Term -> Map Symbol Term -> Maybe (Map Symbol Term)
unifyType a b s = case (substituteType s a, substituteType s b) of
    (a', b') | a' == b' -> Just s
    (Term x [], b') | isTypeVar x -> bind x b'
    (a', Term x []) | isTypeVar x -> bind x a'
    (Term c as, Term d bs)
        | c == d
        , length as == length bs ->
            foldM (\m (x, y) -> unifyType x y m) s (zip as bs)
    _ -> Nothing
  where
    bind x ty = do
        guard (not (occurs x ty))
        Just (Map.insert x ty s)
    occurs x (Term y ts) = (null ts && x == y) || any (occurs x) ts

{- | The subterms of a template that are not template variables, each with
the function that puts a term in its place.
-}
contexts :: Term -> [(Term, Term -> Term)]
contexts t@(Term "app" [ty, f, v]) =
    (t, id)
        : [(u, \x -> Term "app" [ty, put x, v]) | (u, put) <- contexts f]
        ++ [(u, \x -> Term "app" [ty, f, put x]) | (u, put) <- contexts v]
contexts t@(Term x _)
    | isTemplateVar x = []
    | otherwise = [(t, id)]

{- | The critical pairs of two rules whose binders are already apart.
The first rule supplies its contexts and right side. Reuse these contexts
when the first rule is the incoming rule of a completion batch.
-}
criticalPairs :: [(Term, Term -> Term)] -> Term -> (Term, Term) -> [(Term, Term)]
criticalPairs places r1 (l2, r2) =
    [ (substitute s r1, substitute s (put r2))
    | (u, put) <- places
    , unifiableShapes u l2
    , Just s <- [unify u l2]
    ]

{- | Whether the program shapes of two terms can unify: a template variable
fits any annotated subterm, applications fit each other part by part, and
two other terms fit if they have the same symbol. The types are not part of
a shape, and a repeated variable is not checked. 'unify' fails on terms whose
shapes do not fit, so this check is a cheap first test.
-}
unifiableShapes :: Term -> Term -> Bool
unifiableShapes (Term x [_]) (Term _ (_ : _)) | isTemplateVar x = True
unifiableShapes (Term _ (_ : _)) (Term y [_]) | isTemplateVar y = True
unifiableShapes (Term "app" [_, f, v]) (Term "app" [_, g, u]) = unifiableShapes f g && unifiableShapes v u
unifiableShapes (Term c [_]) (Term d [_]) = c == d
unifiableShapes _ _ = False

{- | The critical pairs of a rule with each rule of the index, in the two
orders. Share the incoming rule's renamed terms and left contexts within
this batch. Keep the original binder names and pair order.
-}
criticalPairsWith :: Rules -> (Term, Term) -> [(Term, Term)]
criticalPairsWith rules (l, r) =
    concat
        [ criticalPairs incomingPlaces incomingRight (right oldL, right oldR)
            ++ criticalPairs (contexts (left oldL)) (left oldR) incomingReverse
        | (oldL, oldR) <- allRules rules
        , overlaps oldL
        ]
  where
    apart prefix (Symbol x) = Symbol (prefix <> T.drop 3 x)
    left = rename (apart "<v>L:") (apart "<t>L:")
    right = rename (apart "<v>R:") (apart "<t>R:")
    incomingPlaces = contexts (left l)
    incomingRight = left r
    incomingReverse = (right l, right r)
    -- A rule whose left side fits no place of the incoming left side, and
    -- none of whose places fits the incoming left side, gives no pair (see
    -- 'unifiableShapes'). A renaming keeps the shapes, so the test reads the
    -- rules before their renaming.
    incomingShapes = map fst (contexts l)
    overlaps oldL = any (`unifiableShapes` oldL) incomingShapes || any ((`unifiableShapes` l) . fst) (contexts oldL)

{- | Whether an equation is an instance of a rule of the index, in the same
context on the two sides, as in Twee. Then the equation follows from the
rule. The two sides of the rule match the two sides of the equation with
one substitution, so a rule with a variable on one side only can subsume
too. An equation that the order cannot orient is never ground joinable
with only the ordering of its variables, so without this test the
completion adds it again for each critical pair that gives it.
-}
subsumed :: Rules -> (Term, Term) -> Bool
subsumed rules (s, t) =
    or
        [ True
        | (l, r) <- concatMap (`candidates` s) [oriented rules, unoriented rules, nonRewriting rules]
        , Just m <- [matchTyped l s Map.empty]
        , Just _ <- [matchTemplate r t m]
        ]
        || case (s, t) of
            (Term "app" [ty, f, v], Term "app" [ty', g, u])
                | ty == ty' ->
                    (f == g && subsumed rules (v, u)) || (v == u && subsumed rules (f, g))
            _ -> False

{- | The number of template variables up to which 'groundJoinable' tests
each ordering of the variables.
-}
maxOrderedVars :: Int
maxOrderedVars = 4

{- | Whether an equation is ground joinable: for each ordering of its
template variables, its two sides have the same normal form in the
Knuth-Bendix order under that ordering (Martin and Nipkow, as in Twee).
An ordering can also make variables equal. With more than
'maxOrderedVars' variables, the test uses only the order without a
ranking of the variables, which is weaker.
This check requires closed type annotations. Term-variable orderings do
not cover changes to the annotation order under type substitution.
-}
groundJoinable :: Rules -> (Term, Term) -> Bool
groundJoinable rules (s, t)
    | hasTypeVars s || hasTypeVars t = False
    | length vs > maxOrderedVars = joinableUnder (Map.empty, Map.empty)
    | otherwise = all joinableUnder (orderings vs)
  where
    vs = nubOrd (templateVarLeaves s ++ templateVarLeaves t)
    joinableUnder (merge, rank) = nf (substitute merge s) == nf (substitute merge t)
      where
        nf = normalForm (rankedGreater (rulesOrder rules) rank) rules

{- | The total preorders of the template variables: the variables of a block
are equal, and the blocks have the ranks of their places. Only variables
of one type can be equal. Each preorder gives the substitution that puts
the first variable of a block for the others, and the ranks of the first
variables.
-}
orderings :: [Term] -> [(Map Symbol Term, Map Symbol Int)]
orderings vs =
    [ ( Map.fromList [(x, b) | b : rest <- order, Term x _ <- rest]
      , Map.fromList [(x, i) | (i, Term x _ : _) <- zip [0 ..] order]
      )
    | blocks <- partitions vs
    , order <- permutations blocks
    ]
  where
    partitions [] = [[]]
    partitions (v : rest) =
        concat
            [ ([v] : p) : [before ++ (v : b) : after | (before, b : after) <- splits p, sameType v b]
            | p <- partitions rest
            ]
    splits p = [splitAt i p | i <- [0 .. length p - 1]]
    sameType (Term _ ty) (Term _ ty' : _) = ty == ty'
    sameType _ [] = False

-- | Count all nodes, including annotations, up to a fixed cache limit.
cacheable :: Term -> Bool
cacheable = isJust . within (256 :: Int)
  where
    within 0 _ = Nothing
    within budget (Term symbol children) = symbol `seq` foldM within (budget - 1) children

{- | Reuse a normal form only when both terms have at most 256 nodes.
Check input size before hashing. Clear a full cache on the next insertion.
Keep the normalization function fixed while reusing the cache.
-}
cachedNormalForm :: (Term -> Term) -> HashMap.HashMap Term Term -> Term -> (Term, HashMap.HashMap Term Term)
cachedNormalForm nf cache term
    | not (cacheable term) = (nf term, cache)
    | otherwise = case HashMap.lookup term cache of
        Just result -> (result, cache)
        Nothing ->
            let result = nf term
                next
                    | cacheable result = HashMap.insert term result (if HashMap.size cache >= 256 then HashMap.empty else cache)
                    | otherwise = cache
             in (result, next)

{- | Add a law to the rules, and complete the rules. This is ordered
(unfailing) completion, as Twee does it: each critical pair of a new
rule with a rule of the index becomes an equation, unless its two sides
are ground joinable. The new equation then gives new rules, and its
critical pairs follow. A critical pair whose normal form has a side with
more leaves than the given size is dropped, as in QuickSpec. A separate
annotation-depth budget bounds polymorphic completion. It can omit valid
critical pairs. It is not a coverage bound for the search grammar. The rules of
the critical pairs make the rewriting stronger, so that a law that
follows from the earlier laws is not found again.

With a fuel, the completion takes at most that many critical pairs from its
queue. Then it keeps the rules that it has. They follow from the laws, so
they are sound, but they can prune less than the complete rules. The result
also says whether the fuel ran out, and the number of pairs taken.

With a window n > 1, the completion decides the next critical pairs of
the queue in parallel threads, under the rules of the moment, and takes the
decisions in order. A new equation changes the rules, so the pairs after it
go back to the queue. A decision depends only on the pair and the rules, so
the decisions are the same as without the window. The number of pairs in
parallel starts at 1. It doubles, up to n, after a step without a new
equation. After a new equation at position k, it becomes k + 1. At 1, the
completion decides the next pair on its own thread, with the cache of
normal forms.
-}
addLaw :: Maybe Int -> Int -> Int -> Sig -> Term -> Rules -> (Rules, Bool, Int)
addLaw fuel window maxSize gsig (Term "(==)" [_, l, r]) rules0 =
    complete 1 0 HashMap.empty rules1 (concatMap (criticalPairsWith rules1) new) []
  where
    (new, rules1) = addEquation (toTemplate gsig l, toTemplate gsig r) rules0
    -- Program size does not bound type depth. This explicit budget depends
    -- on the requested size and the declared types. Together with canonical
    -- binders, it gives a finite universe of bounded critical pairs.
    maxAnnotationDepth = (2 * max 0 maxSize + 1) * (1 + maximum (0 : map (typeSize . sfTypeRep) (Map.elems gsig)))
    -- \| Check each annotation after critical-pair normalization.
    withinDepth :: Term -> Bool
    withinDepth (Term "app" [ty, f, v]) = depth ty <= maxAnnotationDepth && withinDepth f && withinDepth v
    withinDepth (Term _ tys) = all ((<= maxAnnotationDepth) . depth) tys
    -- \| The maximum constructor depth of an annotation.
    depth :: Term -> Int
    depth (Term _ ts) = 1 + maximum (0 : map depth ts)
    -- The queue is the current list of critical pairs, then the later lists,
    -- newest first. A new list goes on the front of the later lists, so the
    -- queue is not walked again. Each list stays lazy. The order is FIFO.
    complete _ taken _ rules [] [] = (rules, False, taken)
    complete w taken cache rules [] later = complete w taken cache rules (concat (reverse later)) []
    complete _ taken _ rules _ _ | Just taken == fuel = (rules, True, taken)
    complete w taken _ rules queue later | w > 1 = speculate w taken rules queue later
    complete !w !taken !cache rules ((s, t) : queue) later
        -- The right normal form cannot change this rejection. Keep cache1
        -- because cache2 would force the right normal form.
        | leaves s' > maxSize = complete (grow w) (taken + 1) cache1 rules queue later
        | s' == t'
            || leaves t' > maxSize
            || not (withinDepth s' && withinDepth t')
            || subsumed rules (s', t')
            || groundJoinable rules (s', t') =
            complete (grow w) (taken + 1) cache2 rules queue later
        | otherwise = complete 1 (taken + 1) HashMap.empty rules' queue (concatMap (criticalPairsWith rules') new' : later)
      where
        -- Normalize a critical pair only with decreases that hold for every
        -- type instance. Otherwise normalization can erase a general rule
        -- that its later instances still need.
        nf = normalForm (independentGreater (rulesOrder rules)) rules
        (s', cache1) = cachedNormalForm nf cache s
        (t', cache2) = cachedNormalForm nf cache1 t
        (new', rules') = addEquation (canonical (s', t')) rules
    -- The decision of 'complete' for a pair: Nothing to drop it, or its
    -- normal forms.
    decide rules (s, t)
        | leaves s' > maxSize = Nothing
        | s' == t'
            || leaves t' > maxSize
            || not (withinDepth s' && withinDepth t')
            || subsumed rules (s', t')
            || groundJoinable rules (s', t') =
            Nothing
        | otherwise = Just (s', t')
      where
        nf = normalForm (independentGreater (rulesOrder rules)) rules
        s' = nf s
        t' = nf t
    -- Take the decisions of the next pairs in order, up to the first new
    -- equation.
    speculate w taken rules queue later = go 0 (zip batch (decideInParallel (decide rules) batch))
      where
        (batch, rest, later') = nextPairs (maybe w (min w . subtract taken) fuel) queue later
        go k [] = complete (grow w) (taken + k) HashMap.empty rules rest later'
        go k ((_, Nothing) : more) = go (k + 1) more
        go k ((_, Just pair) : more) =
            let (new', rules') = addEquation (canonical pair) rules
             in complete
                    (k + 1)
                    (taken + k + 1)
                    HashMap.empty
                    rules'
                    (map fst more ++ rest)
                    (concatMap (criticalPairsWith rules') new' : later')
    -- The number of pairs in parallel after a step without a new equation.
    grow w = if window > 1 then min window (2 * w) else w
    -- The next n pairs in FIFO order, the rest of the queue, and the later
    -- lists.
    nextPairs n queue later = case splitAt n queue of
        (batch, rest) | length batch == n || null later -> (batch, rest, later)
        _ -> let (batch, rest) = splitAt n (queue ++ concat (reverse later)) in (batch, rest, [])
addLaw _ _ _ _ _ rules = (rules, False, 0)

{- | Evaluate a function on each element in its own thread, to weak head
normal form. The allocation counter of the caller takes the allocation of
the results up to the first 'Just', because the completion uses these
results. An exception of the caller stops the threads.
-}
decideInParallel :: (a -> Maybe b) -> [a] -> [Maybe b]
{-# NOINLINE decideInParallel #-}
decideInParallel f xs = unsafePerformIO $ mask $ \restore -> do
    started <-
        mapM
            (\x -> do var <- newEmptyMVar; thread <- forkIO (try (restore (measured (f x))) >>= putMVar var); pure (thread, var))
            xs
    results <- restore (mapM (takeMVar . snd) started) `onException` mapM_ (killThread . fst) started
    decided <- either (throwIO :: SomeException -> IO a) pure (sequence results)
    let (dropped, taken) = break (isJust . fst) decided
    left <- getAllocationCounter
    setAllocationCounter (left - sum (map snd (dropped ++ take 1 taken)))
    pure (map fst decided)
  where
    measured y = do
        before <- getAllocationCounter
        result <- evaluate y
        after <- getAllocationCounter
        pure (result, before - after)

-- | The rules of a law alone, without the rules of its critical pairs.
addLawRules :: Sig -> Term -> Rules -> Rules
addLawRules gsig (Term "(==)" [_, l, r]) rules = snd (addEquation (toTemplate gsig l, toTemplate gsig r) rules)
addLawRules _ _ rules = rules

{- | Give term and type binders stable names in their first-occurrence
order. Alpha-equivalent critical pairs then have the same names. Keep the
first type names compatible with the carrier specializations of templates.
-}
canonical :: (Term, Term) -> (Term, Term)
canonical (s, t) = (rename name typeName s, rename name typeName t)
  where
    names = Map.fromList (zip [x | Term x _ <- nubOrd (templateVarLeaves s ++ templateVarLeaves t)] [0 :: Int ..])
    name x = Symbol ("<v>" <> T.pack (show (names Map.! x)))
    typeNames = Map.fromList (zip (nubOrd (types s ++ types t)) [0 :: Int ..])
    typeName x = Symbol ("<t>" <> labels !! (typeNames Map.! x))
    labels = map snd carriers ++ ["p" <> T.pack (show n) | n <- [length carriers ..]]
    types (Term "app" [ty, f, v]) = typeVars ty ++ types f ++ types v
    types (Term _ tys) = concatMap typeVars tys
    typeVars (Term h ts) = [h | null ts, isTypeVar h] ++ concatMap typeVars ts

{- | The spine of a term: its head, a symbol with its annotation, and the
arguments of the applications, from the first.
-}
spine :: Term -> (Term, [Term])
spine (Term "app" [_, f, x]) = let (h, args) = spine f in (h, args ++ [x])
spine t = (t, [])

{- | The place of a function symbol with a number of arguments in the
precedence: the symbols of the list in their order, above the symbols that
it does not give, which are in the order of their names. A symbol with more
arguments is above the same symbol with fewer.
-}
precedenceKey :: [T.Text] -> Symbol -> Int -> (Int, T.Text, Int)
precedenceKey precedence (Symbol name) arity = case elemIndex name precedence of
    Just index -> (index, "", arity)
    Nothing -> (-1, name, arity)

{- | The lexicographic path order on the uncurried templates: whether the
first is greater than the second for each term and type instance in which
the ranked template variables compare as the ranking says.

A template variable is greater only than a variable of a lower rank. A
term is greater than a variable that it contains, or than a variable of a
lower rank than one that it contains. Otherwise a term is greater when an
argument of it is equal to or greater than the other term, or when it is
greater than each argument of the other term and its head is above the
other head in the precedence, or the heads are one symbol with the same
arguments and its arguments are greater from the left. A term whose head is
a template variable is greater only through an argument, or than a term with
the same variable head and lexicographically smaller arguments. The order
reads no type annotation, so it holds for each type instance.
-}
lpoGreater :: [T.Text] -> Map Symbol Int -> Term -> Term -> Bool
lpoGreater precedence rank = greater
  where
    greater s t
        | s == t = False
        | otherwise = case (spine s, spine t) of
            ((Term x [_], []), _)
                | isTemplateVar x -> case spine t of
                    (Term y [_], []) | isTemplateVar y -> above x y
                    _ -> False
            (_, (Term y [_], []))
                | isTemplateVar y -> y `elem` templateVars s || any (`above` y) (templateVars s)
            ((Term f [_], ss), (Term g [_], ts)) ->
                any (\si -> si == t || greater si t) ss
                    || ( not (isTemplateVar f)
                            && not (isTemplateVar g)
                            && precedenceKey precedence f (length ss) > precedenceKey precedence g (length ts)
                            && all (greater s) ts
                       )
                    || (f == g && length ss == length ts && lexicographic ss ts && all (greater s) ts)
            _ -> False
    above x y = case (Map.lookup x rank, Map.lookup y rank) of
        (Just i, Just j) -> i > j
        _ -> False
    lexicographic (a : as) (b : bs)
        | a == b = lexicographic as bs
        | otherwise = greater a b
    lexicographic _ _ = False

{- | The lexicographic path order on ground terms, total: the generated
variables are constants below all function symbols, in the order of their
names. The path order compares the terms without their type annotations.
Two terms that differ only in their type annotations compare by the
annotations. Thus the order is transitive.
-}
lpoCompare :: [T.Text] -> (Symbol -> Bool) -> Term -> Term -> Ordering
lpoCompare precedence isVar s t
    | s == t = EQ
    | greater s t = GT
    | greater t s = LT
    | otherwise = compare s t
  where
    key symbol@(Symbol name) arity
        | isVar symbol = (-2 :: Int, name, arity)
        | otherwise = precedenceKey precedence symbol arity
    greater a b = case (spine a, spine b) of
        ((Term f [_], as), (Term g [_], bs)) ->
            any (\ai -> erasedEqual ai b || greater ai b) as
                || (key f (length as) > key g (length bs) && all (greater a) bs)
                || (f == g && length as == length bs && lexicographic as bs && all (greater a) bs)
        _ -> False
    lexicographic (a : as) (b : bs)
        | erasedEqual a b = lexicographic as bs
        | otherwise = greater a b
    lexicographic _ _ = False
    erasedEqual (Term "app" [_, f, x]) (Term "app" [_, g, y]) = erasedEqual f g && erasedEqual x y
    erasedEqual (Term f [_]) (Term g [_]) = f == g
    erasedEqual a b = a == b
