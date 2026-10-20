{- | Lower shared predicate definitions to the existing SMT formula fragment.

Lowering preserves the complete formula. It does not replace native functions
by uninterpreted functions, project data values to integers, or discard
unsupported arguments.
-}
module Data.CFTA.Lean.Lower (
    lower,
) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Data.CFTA.Formula (
    Formula (..),
    Name,
    Sort (..),
    Term (..),
    substituteChecked,
 )
import Data.CFTA.Lean.Formula (renderEntailment)
import Data.CFTA.Lean.Theory (Theory)
import qualified Data.CFTA.Lean.Theory as Theory

{- | Validate a formula, then unfold its shared predicate definitions.

A shared definition can refer to its parameters, locally bound values, and
other shared predicates. Substitution avoids variable capture. Recursive
definitions, duplicate binders, native predicates, native functions, and
named data sorts are rejected.

Every declaration must have an SMT sort. An unused value can have an empty
Lean type, so its quantifier cannot be discarded. All original arguments are
checked before a definition is unfolded.
An unused argument therefore cannot hide a native function or a data value.
Predicate names are global. A value binder does not bind a predicate name.

The result is exact for the supported fragment. A failure is not evidence
for either validity or invalidity.
-}
lower :: Theory -> [(Name, Sort)] -> Formula -> Either String Formula
lower theory declarations original = do
    _ <- renderEntailment theory declarations [] [] Top original
    unless (Map.size definitions == length theory) (Left "The theory contains duplicate names")
    mapM_ (checkSort . snd) declarations
    inFormula Set.empty Nothing original
  where
    definitions = Map.fromList theory

    -- Unfold predicates and check every part of the original formula.
    inFormula :: Set Name -> Maybe (Set Name) -> Formula -> Either String Formula
    inFormula active scope formula = case formula of
        Top -> Right Top
        Bottom -> Right Bottom
        And parts -> And <$> traverse recurse parts
        Or parts -> Or <$> traverse recurse parts
        Not inner -> Not <$> recurse inner
        Atom relation left right -> Atom relation <$> term left <*> term right
        Forall bindings inner -> under Forall bindings inner
        Exists bindings inner -> under Exists bindings inner
        Predicate name arguments -> do
            lowered <- traverse term arguments
            case Map.lookup name definitions of
                Just (Theory.Defined parameters body) -> do
                    checkBindings parameters
                    unless (length parameters == length lowered) (Left "A shared predicate has incorrect arity")
                    unless (name `Set.notMember` active) (Left "Shared predicates contain a definition cycle")
                    expanded <- inFormula (Set.insert name active) (Just (Set.fromList (map fst parameters))) body
                    case substituteChecked (zip (map fst parameters) lowered) expanded of
                        Left problem -> Left ("A shared predicate cannot be substituted: " <> show problem)
                        Right result -> Right result
                Just (Theory.Predicate _ _) -> Left "A native Lean predicate cannot be lowered"
                _ -> Left "A predicate has no shared definition"
      where
        recurse = inFormula active scope
        term = inTerm active scope
        under constructor bindings inner = do
            checkBindings bindings
            constructor bindings <$> inFormula active (fmap (<> Set.fromList (map fst bindings)) scope) inner

    -- Check terms without replacing native definitions by SMT symbols.
    inTerm :: Set Name -> Maybe (Set Name) -> Term -> Either String Term
    inTerm active scope term = case term of
        Lit _ -> Right term
        Var name -> checkName scope name >> Right term
        App name arguments -> do
            checkName scope name
            App name <$> traverse recurse arguments
        Neg inner -> Neg <$> recurse inner
        Add left right -> Add <$> recurse left <*> recurse right
        Sub left right -> Sub <$> recurse left <*> recurse right
        Mul left right -> Mul <$> recurse left <*> recurse right
        Div left right -> Div <$> recurse left <*> recurse right
        Mod left right -> Mod <$> recurse left <*> recurse right
        Ite condition yes no ->
            Ite <$> inFormula active scope condition <*> recurse yes <*> recurse no
        Cast inner sort -> do
            checkSort sort
            (`Cast` sort) <$> recurse inner
      where
        recurse = inTerm active scope

    -- Shared bodies have no implicit free values or free functions.
    checkName :: Maybe (Set Name) -> Name -> Either String ()
    checkName scope name = do
        case Map.lookup name definitions of
            Just Theory.Function{} -> Left "A native Lean function cannot be lowered"
            Just (Theory.TypeConstructor _ _) -> Left "A type constructor cannot be used as an SMT value"
            _ -> Right ()
        case scope of
            Nothing -> Right ()
            Just locals ->
                unless (name `Set.member` locals) (Left "A shared predicate body contains a free value or function")

-- | Reject duplicate binders and all named data sorts.
checkBindings :: [(Name, Sort)] -> Either String ()
checkBindings bindings = do
    unless (Set.size (Set.fromList (map fst bindings)) == length bindings) (Left "A binder list contains duplicate names")
    mapM_ (checkSort . snd) bindings

-- | Keep the sorts of the existing SMT formula language.
checkSort :: Sort -> Either String ()
checkSort sort = case sort of
    IntSort -> Right ()
    RealSort -> Right ()
    BoolSort -> Right ()
    FunctionSort arguments result -> mapM_ checkSort arguments >> checkSort result
    NamedSort _ _ -> Left "A named data sort cannot be lowered"
