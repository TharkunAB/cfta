{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TypeApplications #-}

{- | Typed arithmetic, a language of "Data.CFTA.Gen.Typing" with literals, a
comparison, a conditional whose type is the type of its branches,
let-binding, and variables without a type: its datatype, its rules, and a
type checker.
-}
module Data.CFTA.Gen.TypedArithmeticLanguage (
    ArithType (..),
    Arith (..),
    ArithNode (..),
    arithRules,
    arithOperatorRules,
    arithTyping,
    arithLanguage,
    arithAutomaton,
    subterms,
    arithType,
    arithNesting,
) where

import GHC.Generics (Generic)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint)
import qualified Data.CFTA.Gen as Gen
import Data.CFTA.Gen.Refinement.Derive (NodeView)
import Data.CFTA.Gen.Typing (
    Bound (..),
    Rule,
    Typing (Typing),
    TypingState,
    fromTypingRules,
    rule,
    subterm,
    typingAutomaton,
    value,
    variable,
 )
import Data.CFTA.Generic (Constructor, HasFTA)
import Data.CFTA.Symbol (Symbol)

-- | The types of the arithmetic language.
data ArithType = IntType | BoolType
    deriving stock (Eq, Ord, Show)

-- | Arithmetic with literals, a comparison, a conditional, and let-binding. A variable has no type.
data Arith
    = Num !Int
    | Flag !Bool
    | Plus Arith Arith
    | Less Arith Arith
    | If Arith Arith Arith
    | Var !Int
    | Let Arith Arith
    | Arg !Int
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (HasFTA)

-- | One node of a typed arithmetic term: for the typing rules, and for the invariants of the refinement tests.
data ArithNode e
    = NumNode e
    | FlagNode e
    | PlusNode e e
    | LessNode e e
    | IfNode e e e
    | VarNode e
    | LetNode e e
    | ArgNode e
    deriving stock (Generic)
    deriving anyclass (NodeView)

-- | The typing rules of 'Arith': the literals 0 and 1, and 'arithOperatorRules'.
arithRules :: [Rule ArithNode ArithType]
arithRules = [rule (NumNode (value n)) IntType | n <- [0, 1 :: Int]] <> arithOperatorRules

-- | The typing rules of 'Arith' other than the numbers. The type of a conditional is the type of its branches.
arithOperatorRules :: [Rule ArithNode ArithType]
arithOperatorRules =
    [rule (FlagNode (value b)) BoolType | b <- [False, True]]
        <> [ rule (PlusNode (subterm [] IntType) (subterm [] IntType)) IntType
           , rule (LessNode (subterm [] IntType) (subterm [] IntType)) BoolType
           , variable (\index _ -> VarNode (value index))
           ]
        <> [rule (IfNode (subterm [] BoolType) (subterm [] typ) (subterm [] typ)) typ | typ <- [IntType, BoolType]]
        <> [rule (LetNode (subterm [] rhs) (subterm [rhs] typ)) typ | rhs <- [IntType, BoolType], typ <- [IntType, BoolType]]

-- | The typed arithmetic language up to the bound.
arithTyping :: Int -> Typing ArithNode ArithType
arithTyping bound = Typing (Nesting (fromIntegral bound)) [] [IntType, BoolType] arithRules

-- | The closed well-typed arithmetic terms up to the bound, from the rules.
arithLanguage :: Int -> Gen.Gen Symbol Arith
arithLanguage = either (error . show) id . fromTypingRules . arithTyping

-- | The automaton of the closed well-typed arithmetic terms up to the bound.
arithAutomaton :: Int -> FTA.FTA (TypingState ArithType) Constructor Constraint
arithAutomaton = either (error . show) id . typingAutomaton @Arith . arithTyping

-- | The subterms of an arithmetic term, the term first.
subterms :: Arith -> [Arith]
subterms term =
    term
        : concatMap
            subterms
            ( case term of
                Plus left right -> [left, right]
                Less left right -> [left, right]
                If condition yes no -> [condition, yes, no]
                Let rhs body -> [rhs, body]
                _ -> []
            )

-- | The type of an arithmetic term in an environment, if it has one, with the literals of the rules.
arithType :: [ArithType] -> Arith -> Maybe ArithType
arithType _ (Num n) = if n `elem` [0, 1] then Just IntType else Nothing
arithType _ (Flag _) = Just BoolType
arithType _ (Arg _) = Nothing
arithType env (Plus left right) = do
    IntType <- arithType env left
    IntType <- arithType env right
    Just IntType
arithType env (Less left right) = do
    IntType <- arithType env left
    IntType <- arithType env right
    Just BoolType
arithType env (If condition yes no) = do
    BoolType <- arithType env condition
    typ <- arithType env yes
    other <- arithType env no
    if typ == other then Just typ else Nothing
arithType env (Var index)
    | index >= 0, index < length env = Just (env !! index)
    | otherwise = Nothing
arithType env (Let rhs body) = do
    rhsType <- arithType env rhs
    arithType (rhsType : env) body

-- | The nesting of an arithmetic term: the constructors with subterms on the longest path.
arithNesting :: Arith -> Int
arithNesting term = case term of
    Plus left right -> 1 + max (arithNesting left) (arithNesting right)
    Less left right -> 1 + max (arithNesting left) (arithNesting right)
    If condition yes no -> 1 + maximum (map arithNesting [condition, yes, no])
    Let rhs body -> 1 + max (arithNesting rhs) (arithNesting body)
    _ -> 0
