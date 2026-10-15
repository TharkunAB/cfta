{- | Normal forms of programs, from the bodies of their components.

Two fits that differ in text can be one program: @flip filter xs p@ is
@filter p xs@, and @fst (x, y)@ is @x@. The normal form makes them equal. The
bodies come from GHC: the unfolding of each candidate's identifier, in Core,
which the session reads from the interfaces when it does not ignore
interface pragmas (@-fno-ignore-interface-pragmas@). A body translates to a
term without types, casts, ticks, coercions, and call-stack dictionaries
('termOfId').

An identifier stays an opaque leaf when its body does not translate in full:

* a class method, a dictionary function, or a primop;
* an identifier without an unfolding;
* a body with a class dictionary, as a binder or as an argument: a program
  has no dictionaries, so two instances would look the same;
* a body with a recursive @let@;
* an identifier whose own unfolding is in progress (a cycle): the inner
  occurrence is a leaf.

The normal form ('normalForm') evaluates a program with these bodies. It
uses beta, the eta-expansion of known functions, the eta law of pairs (the
pair of the two projections of one value is that value), a case of a known
constructor, a case of a case, and the identity case. A case on a leaf is a
stuck case. Its alternatives come in the order of the constructor tags, and
a default alternative expands to the missing constructors when the type is
known.

The normal form is a lower bound of equality: two programs with the same
normal form are equal, and two equal programs can have different normal
forms, when an equality needs a body that does not translate, as the body of
a recursive function. The eta law of pairs is wrong for @undefined@ (the pair
of its projections is not @undefined@), and the normal form keeps it.
-}
module Data.CFTA.GHC.NormalForm (
    -- * Terms
    Term,
    termOfId,

    -- * Normal forms
    NormalForm,
    normalForm,
    mentions,
) where

import Data.Bifunctor (first)
import Data.Either (lefts, rights)
import Data.List (elemIndex, sortOn)
import Data.Maybe (isJust, listToMaybe)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text

import Data.CFTA.Gen.Synthesis (Program)
import qualified Data.CFTA.Gen.Synthesis as Synthesis
import GHC.Builtin.Types (tupleDataCon)
import GHC.Core (Alt (..), AltCon (..), Bind (..), CoreExpr, Expr (..), Unfolding (..))
import GHC.Core.DataCon (DataCon, dataConName, dataConRepArity, dataConTag, dataConTyCon, isVanillaDataCon)
import GHC.Core.Predicate (isCallStackPredTy, isPredTy)
import GHC.Core.TyCon (tyConDataCons)
import GHC.Core.Utils (exprType)
import GHC.Types.Basic (Boxity (Boxed))
import GHC.Types.Id (idType, isClassOpId, isDFunId, isDataConWorkId_maybe, isPrimOpId, realIdUnfolding)
import GHC.Types.Name (Name, getName, isExternalName, nameStableString)
import GHC.Types.Var (Id, Var, isCoVar, isTyVar)
import GHC.Utils.Outputable (showPprUnsafe)

-- | A constructor: its key, its tag, its number of fields, and the constructors of its type.
data Con = Con
    { conKey :: !Text
    , conTag :: !Int
    , conArity :: !Int
    , conFamily :: [Con]
    }

-- | The key of an alternative: a constructor, or a literal.
data AltKey = ByCon Con | ByLiteral Text

-- | The text of an alternative's key.
altText :: AltKey -> Text
altText key = case key of
    ByCon con -> conKey con
    ByLiteral literal -> literal

{- | A term: Core without types. A variable is a de Bruijn index. A global
has its key, and its body when it unfolds.
-}
data Term
    = TVar !Int
    | TGlobal !Text (Maybe Term)
    | TCon Con
    | TApp Term Term
    | TLam Term
    | -- | A non-recursive @let@: the right side, and the body, which binds index 0.
      TLet Term Term
    | {- | A case: the scrutinee, the alternatives with their number of fields,
      and the default. An alternative binds the case binder, then its fields
      (the last field is index 0); the default binds the case binder.
      -}
      TCase Term [(AltKey, Int, Term)] (Maybe Term)
    | -- | A literal, or a call-stack dictionary.
      TOpaque !Text

-- | The key of a name, the same in each module of the session.
keyOf :: Name -> Text
keyOf = Text.pack . nameStableString

-- | The key of the pair constructor, for the eta law of pairs.
pairKey :: Text
pairKey = keyOf (dataConName (tupleDataCon Boxed 2))

-- | The constructor of a data constructor, with the constructors of its type.
conOf :: DataCon -> Con
conOf constructor = Con (keyOf (dataConName constructor)) (dataConTag constructor) (dataConRepArity constructor) family
  where
    family = map conOf (tyConDataCons (dataConTyCon constructor))

-- | The term of an identifier: a constructor, its body when it unfolds, or else an opaque global.
termOfId :: Id -> Term
termOfId = global Set.empty

-- | The term of a global, with the globals whose unfolding is in progress.
global :: Set.Set Name -> Id -> Term
global stack identifier
    | Just constructor <- isDataConWorkId_maybe identifier =
        if isVanillaDataCon constructor then TCon (conOf constructor) else opaque
    | isClassOpId identifier || isDFunId identifier || isPrimOpId identifier = opaque
    | name `Set.member` stack = opaque
    | CoreUnfolding{uf_tmpl = template} <- realIdUnfolding identifier
    , Just body <- translate (Set.insert name stack) [] template =
        TGlobal key (Just body)
    | otherwise = opaque
  where
    name = getName identifier
    key = keyOf name
    opaque = TGlobal key Nothing

-- | Whether a variable is a call-stack dictionary.
isCallStack :: Var -> Bool
isCallStack variable = isCallStackPredTy (idType variable)

-- | Whether a variable is a dictionary of a class.
isDictionary :: Var -> Bool
isDictionary variable = isPredTy (idType variable)

{- | Translate Core with the local variables in scope (the innermost first).
'Nothing' when a part does not translate.
-}
translate :: Set.Set Name -> [Var] -> CoreExpr -> Maybe Term
translate stack scope expression = case expression of
    Var variable
        | isExternalName (getName variable) -> Just (global stack variable)
        | isCallStack variable -> Just callStack
        | isDictionary variable -> Nothing
        | otherwise -> TVar <$> elemIndex variable scope
    Lit literal -> Just (TOpaque (Text.pack ("literal " <> showPprUnsafe literal)))
    App function argument -> case argument of
        Type _ -> go function
        Coercion _ -> go function
        _
            | isPredTy (exprType argument) ->
                if isCallStackPredTy (exprType argument) then go function else Nothing
            | otherwise -> TApp <$> go function <*> go argument
    Lam binder body
        | isTyVar binder || isCoVar binder -> go body
        | isCallStack binder -> go body
        | isDictionary binder -> Nothing
        | otherwise -> TLam <$> translate stack (binder : scope) body
    Let (NonRec binder right) body
        | isTyVar binder || isCoVar binder -> go body
        | isCallStack binder -> go body
        | isDictionary binder -> Nothing
        | otherwise -> TLet <$> go right <*> translate stack (binder : scope) body
    Let (Rec _) _ -> Nothing
    Case scrutinee binder _ alternatives -> do
        scrutinee' <- go scrutinee
        translated <- traverse (alternative binder) alternatives
        pure (TCase scrutinee' (lefts translated) (listToMaybe (rights translated)))
    Cast inner _ -> go inner
    Tick _ inner -> go inner
    Type _ -> Nothing
    Coercion _ -> Nothing
  where
    go = translate stack scope
    callStack = TOpaque (Text.pack "call stack")
    alternative binder (Alt constructor fields right) = case constructor of
        DataAlt dataCon
            | isVanillaDataCon dataCon -> do
                let values = filter (\field -> not (isTyVar field || isCoVar field)) fields
                right' <- translate stack (reverse values <> (binder : scope)) right
                pure (Left (ByCon (conOf dataCon), length values, right'))
            | otherwise -> Nothing
        LitAlt literal -> do
            right' <- translate stack (binder : scope) right
            pure (Left (ByLiteral (Text.pack ("literal " <> showPprUnsafe literal)), 0, right'))
        DEFAULT -> Right <$> translate stack (binder : scope) right

-- | The head of a neutral value: a global, a leaf of the program, or a bound variable of an eta-expansion.
data Head = Global Text | Leaf Text | Bound Int
    deriving (Eq, Ord, Show)

-- | A value of the evaluator.
data Value
    = VNeutral Head [Value]
    | VLam (Value -> Value)
    | VCon Con [Value]
    | -- | A stuck case: its alternatives have the case binder (the scrutinee) and take their fields.
      VCase Value [(AltKey, Int, [Value] -> Value)] (Maybe Value)

-- | The normal form of a program.
data NormalForm
    = NNeutral Head [NormalForm]
    | NLam NormalForm
    | NCon Text [NormalForm]
    | NCase NormalForm [(Text, NormalForm)] (Maybe NormalForm)
    deriving (Eq, Ord, Show)

{- | The normal form of a program. The function gives the term of a leaf; a
leaf without a term (an argument of the query) stays a leaf. 'Nothing' when
the normal form has more than a fixed number of nodes.
-}
normalForm :: (Text -> Maybe Term) -> Program -> Maybe NormalForm
normalForm termOf program =
    let normal = quote 0 (evaluateProgram program)
     in if sizeAtMost 20000 normal then Just normal else Nothing
  where
    evaluateProgram leaf = case leaf of
        Synthesis.Var name -> maybe (VNeutral (Leaf name) []) (valueOf []) (termOf name)
        Synthesis.App function argument -> apply (evaluateProgram function) (evaluateProgram argument)

-- | Evaluate a term in an environment.
valueOf :: [Value] -> Term -> Value
valueOf environment term = case term of
    TVar index -> environment !! index
    TGlobal _ (Just body) -> valueOf [] body
    TGlobal key Nothing -> VNeutral (Global key) []
    TCon con -> construct con []
    TApp function argument -> apply (valueOf environment function) (valueOf environment argument)
    TLam body -> VLam (\value -> valueOf (value : environment) body)
    TLet right body -> valueOf (valueOf environment right : environment) body
    TCase scrutinee alternatives fallback ->
        caseOn
            (valueOf environment scrutinee)
            [ (key, count, \binder fields -> valueOf (reverse fields <> (binder : environment)) right)
            | (key, count, right) <- alternatives
            ]
            ((\right binder -> valueOf (binder : environment) right) <$> fallback)
    TOpaque text -> VNeutral (Global text) []

-- | A constructor that takes its remaining fields.
construct :: Con -> [Value] -> Value
construct con fields
    | length fields >= conArity con = VCon con fields
    | otherwise = VLam (\field -> construct con (fields <> [field]))

-- | Apply a value to an argument.
apply :: Value -> Value -> Value
apply function argument = case function of
    VLam f -> f argument
    VNeutral h arguments -> VNeutral h (arguments <> [argument])
    -- An argument of a stuck case goes into each alternative.
    VCase scrutinee alternatives fallback ->
        VCase
            scrutinee
            [(key, count, \fields -> apply (right fields) argument) | (key, count, right) <- alternatives]
            ((`apply` argument) <$> fallback)
    -- A full constructor takes no argument in a typed program.
    other@VCon{} -> other

-- | A case on a value, with alternatives that take the case binder and the fields.
caseOn :: Value -> [(AltKey, Int, Value -> [Value] -> Value)] -> Maybe (Value -> Value) -> Value
caseOn scrutinee alternatives fallback = case scrutinee of
    VCon con fields -> case [right | (ByCon con', _, right) <- alternatives, conKey con' == conKey con] of
        right : _ -> right scrutinee fields
        [] -> maybe stuck ($ scrutinee) fallback
    -- A function is a value: only the default matches it.
    VLam _ -> maybe stuck ($ scrutinee) fallback
    -- A case of a case: the outer case goes into each inner alternative.
    VCase inner innerAlternatives innerFallback ->
        VCase
            inner
            [(key, count, \fields -> caseOn (right fields) alternatives fallback) | (key, count, right) <- innerAlternatives]
            ((\right -> caseOn right alternatives fallback) <$> innerFallback)
    VNeutral (Global text) []
        | right : _ <- [right | (ByLiteral literal, _, right) <- alternatives, literal == text] -> right scrutinee []
    VNeutral{} -> stuck
  where
    stuck = VCase scrutinee [(key, count, right scrutinee) | (key, count, right) <- alternatives] (($ scrutinee) <$> fallback)

-- | The normal form of a value, with the variables of eta-expansions and alternatives named by their depth.
quote :: Int -> Value -> NormalForm
quote depth value = case value of
    VNeutral h arguments -> NNeutral h (map (quote depth) arguments)
    VLam f -> NLam (quote (depth + 1) (f (VNeutral (Bound depth) [])))
    VCon con fields -> case map (quote depth) fields of
        -- The pair of the two projections of one value is that value.
        [NCase left [(leftKey, NNeutral (Bound l) [])] Nothing, NCase right [(rightKey, NNeutral (Bound r) [])] Nothing]
            | conKey con == pairKey
            , leftKey == pairKey
            , rightKey == pairKey
            , l == depth
            , r == depth + 1
            , left == right ->
                left
        quoted -> NCon (conKey con) quoted
    VCase scrutinee alternatives fallback ->
        let scrutinee' = quote depth scrutinee
            explicit =
                [ (key, quote (depth + count) (right [VNeutral (Bound (depth + i)) [] | i <- [0 .. count - 1]]))
                | (key, count, right) <- alternatives
                ]
            family = case [conFamily con | (ByCon con, _, _) <- alternatives] of
                cons : _ -> cons
                [] -> []
            present = Set.fromList [altText key | (key, _, _) <- alternatives]
            -- A default expands to the constructors that have no alternative.
            expanded = case fallback of
                Just right
                    | not (null family) ->
                        [(conKey con, quote (depth + conArity con) right) | con <- family, not (conKey con `Set.member` present)]
                _ -> []
            fallback'
                | null family = quote depth <$> fallback
                | otherwise = Nothing
            tags = [(conKey con, conTag con) | con <- family]
            ordered = sortOn (\(key, _) -> (lookup key tags, key)) (map (first altText) explicit <> expanded)
            -- An alternative that rebuilds its constructor, or gives the scrutinee.
            identity (key, right) =
                right == scrutinee'
                    || right == NCon key [NNeutral (Bound (depth + i)) [] | i <- [0 .. arityOf key - 1]]
            arityOf key = maybe 0 conArity (lookup key [(conKey con, con) | con <- family])
            complete = not (null family) && length ordered == length family
         in if (complete && all identity ordered) || (null ordered && fallback' == Just scrutinee')
                then scrutinee'
                else NCase scrutinee' ordered fallback'

-- | Whether a normal form has at most the given number of nodes.
sizeAtMost :: Int -> NormalForm -> Bool
sizeAtMost limit normal = isJust (go limit [normal])
  where
    go budget forms
        | budget < 0 = Nothing
        | otherwise = case forms of
            [] -> Just budget
            form : rest -> case form of
                NNeutral _ arguments -> go (budget - 1) (arguments <> rest)
                NLam inner -> go (budget - 1) (inner : rest)
                NCon _ fields -> go (budget - 1) (fields <> rest)
                NCase scrutinee alternatives fallback -> go (budget - 1) (scrutinee : map snd alternatives <> maybe [] pure fallback <> rest)

-- | Whether a leaf of the program occurs in a normal form.
mentions :: NormalForm -> Text -> Bool
mentions normal name = name `Set.member` leaves normal
  where
    leaves form = case form of
        NNeutral (Leaf leaf) arguments -> Set.insert leaf (foldMap leaves arguments)
        NNeutral _ arguments -> foldMap leaves arguments
        NLam inner -> leaves inner
        NCon _ fields -> foldMap leaves fields
        NCase scrutinee alternatives fallback -> leaves scrutinee <> foldMap (leaves . snd) alternatives <> foldMap leaves fallback
