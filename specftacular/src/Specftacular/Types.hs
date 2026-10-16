{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}

module Specftacular.Types where

import Control.Applicative ((<|>))
import Control.Monad (foldM)
import Data.Dynamic
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)
import GHC.Generics (Generic)

import Control.Exception (Exception, SomeException, evaluate, fromException, throw, throwIO, try)
import Data.CFTA.Symbol (Symbol (Symbol))
import qualified Data.CFTA.Term as CT
import Data.Maybe (fromMaybe, mapMaybe)
import Data.Proxy
import qualified Data.Text as T
import Data.Typeable
import Debug.Trace (trace)

import GHC.Exts (Any)
import Test.QuickCheck (Arbitrary (..), Gen (..))
import qualified Test.QuickCheck as QC
import Test.QuickCheck.Gen (unGen)
import Test.QuickCheck.Gen.Unsafe (promote)
import Test.QuickCheck.Random (mkQCGen)
import Specftacular.Polymorphic (applyType, functionType, specialiseDynamic)
import qualified Type.Reflection as TR
import Unsafe.Coerce

import Data.Containers.ListUtils (nubOrd)
import Data.Hashable (Hashable, hash)
import Data.Set (Set)
import qualified Data.Set as Set

{- | A type: a type variable, a function type, or a type constructor with
its arguments.
-}
data TypeSkeleton
    = TVar Text
    | TFun TypeSkeleton TypeSkeleton
    | TCons Text [TypeSkeleton]
    deriving (Eq, Ord, Show, Read, Generic)

instance Hashable TypeSkeleton

-- | The number of constructors and variables in a type.
typeSize :: TypeSkeleton -> Int
typeSize (TCons _ args) = 1 + sum (map typeSize args)
typeSize (TFun a b) = 1 + typeSize a + typeSize b
typeSize (TVar _) = 1

-- | Count concrete leaves to put abstract carrier instances first.
concreteTypeLeaves :: TypeSkeleton -> Int
concreteTypeLeaves t | t `elem` map fst carriers = 0
concreteTypeLeaves (TCons _ []) = 1
concreteTypeLeaves (TCons _ args) = sum (map concreteTypeLeaves args)
concreteTypeLeaves (TFun a b) = concreteTypeLeaves a + concreteTypeLeaves b
concreteTypeLeaves (TVar _) = 0

-- | A term of the automata. The symbols are interned texts.
type Term = CT.Term Symbol

-- | A term as its symbol and the list of its children.
pattern Term :: Symbol -> [Term] -> Term
pattern Term s ts = CT.Node s ts

{-# COMPLETE Term #-}

-- The matcher inlines, as the matcher of 'CT.Node' does, so that a match
-- does not build the list of the children.
{-# INLINE Term #-}

{- | The types that stand for type variables in a signature. Each type has
many values, so that a law that holds only for a small type does not
pass the tests. QuickSpec tests type variables at Int too.
-}
newtype A = A Int deriving (Typeable, Eq, Show, Ord)

newtype B = B Int deriving (Typeable, Eq, Show, Ord)
newtype C = C Int deriving (Typeable, Eq, Show, Ord)
newtype D = D Int deriving (Typeable, Eq, Show, Ord)
newtype Acc = Acc Int deriving (Typeable, Eq, Show, Ord)

deriving instance Arbitrary A
deriving instance QC.CoArbitrary A
deriving instance Arbitrary B
deriving instance QC.CoArbitrary B
deriving instance Arbitrary C
deriving instance QC.CoArbitrary C
deriving instance Arbitrary D
deriving instance QC.CoArbitrary D
deriving instance Arbitrary Acc
deriving instance QC.CoArbitrary Acc

data GeneratedInstance = Gend
    { g_tr :: TypeRep
    , g_arb :: DynGen
    , g_eq :: Maybe Dynamic
    , g_li_i :: GeneratedInstance
    }

{- | The generator and the equality of a type, for the search: the type as
'TypeRep' shows it, the prefix of the names of its variables, the
generator, and the equality, if the type has one.
-}
data Instance = Instance
    { inst_text :: Text
    , inst_prefix :: Text
    , inst_gen :: Generator
    , inst_eq :: Maybe Value
    }

-- | The instance of a generated instance.
toInstance :: GeneratedInstance -> Instance
toInstance rep =
    Instance
        { inst_text = T.pack (show (g_tr rep))
        , inst_prefix = namePrefix (g_tr rep)
        , inst_gen = generator (g_arb rep)
        , inst_eq = dynamicValue <$> g_eq rep
        }

{- | The instances of the types that the signatures of the benchmarks use
(see 'builtinReps'), of A to Acc for the type variables, of the lists of
these, and of the types that the function gives.
-}
frontInstances :: (TypeSkeleton -> Maybe GeneratedInstance) -> TypeSkeleton -> Maybe Instance
frontInstances extraReps t = case genRep t of
    Just rep -> Just (toInstance rep)
    Nothing -> trace ("*** Warning: Could not generate instances for '" ++ show t ++ "', ignoring...") Nothing
  where
    genRep :: TypeSkeleton -> Maybe GeneratedInstance
    genRep (TVar a) | Just t <- lookup a [(v, t) | (t, v) <- carriers] = genRep t
    genRep t | Just g <- extraReps t = Just g
    genRep t | Just g <- lookup t builtinReps = Just g
    genRep (TCons "[]" [ts]) = g_li_i <$> genRep ts
    genRep (TFun a b) = do
        CoarbitraryType (Proxy :: Proxy x) <- coarbitraryType a
        result <- genRep b
        case g_arb result of
            DynGen g -> Just $ generatedNoEq $ DynGen $ promote (\(x :: x) -> QC.coarbitrary x g)
    genRep _ = Nothing

-- | A type with the evidence needed to generate functions from it.
data CoarbitraryType where
    CoarbitraryType :: (Typeable a, QC.CoArbitrary a) => Proxy a -> CoarbitraryType

-- | Resolve function domains from the built-in types, lists, and pairs.
coarbitraryType :: TypeSkeleton -> Maybe CoarbitraryType
coarbitraryType (TVar a) = lookup a [(v, t) | (t, v) <- carriers] >>= coarbitraryType
coarbitraryType (TCons "[]" [a]) = do
    CoarbitraryType (Proxy :: Proxy x) <- coarbitraryType a
    return (CoarbitraryType (Proxy :: Proxy [x]))
coarbitraryType (TCons "(,)" [a, b]) = do
    CoarbitraryType (Proxy :: Proxy x) <- coarbitraryType a
    CoarbitraryType (Proxy :: Proxy y) <- coarbitraryType b
    return (CoarbitraryType (Proxy :: Proxy (x, y)))
coarbitraryType t = lookup t types
  where
    types =
        [ entry (Proxy :: Proxy A)
        , entry (Proxy :: Proxy B)
        , entry (Proxy :: Proxy C)
        , entry (Proxy :: Proxy D)
        , entry (Proxy :: Proxy Acc)
        , entry (Proxy :: Proxy ())
        , entry (Proxy :: Proxy Int)
        , entry (Proxy :: Proxy Integer)
        , entry (Proxy :: Proxy Bool)
        , entry (Proxy :: Proxy Char)
        , entry (Proxy :: Proxy Word)
        , entry (Proxy :: Proxy Double)
        , entry (Proxy :: Proxy Float)
        , entry (Proxy :: Proxy Ordering)
        ]
    entry :: (Typeable a, QC.CoArbitrary a) => Proxy a -> (TypeSkeleton, CoarbitraryType)
    entry p = (typeSkeletonOf p, CoarbitraryType p)

-- | A generator with its type and list generator, without function equality.
generatedNoEq :: DynGen -> GeneratedInstance
generatedNoEq dg@(DynGen (g :: Gen a)) =
    Gend
        { g_tr = typeRep (Proxy :: Proxy a)
        , g_arb = dg
        , g_eq = Nothing
        , g_li_i = generatedNoEq (DynGen (QC.listOf g))
        }

{- | The argument and result types that need generators, and their list
types. A function type needs a generator when it is an argument, as in
map or bind. The full type of each signature function does not need a
generated variable.
-}
instanceTypes :: (TypeSkeleton -> TypeSkeleton) -> Sig -> [TypeSkeleton]
instanceTypes typeMod sigs = nubOrd $ concatMap addLi $ Set.toList $ Set.unions $ map cons trs
  where
    trs = map (typeMod . sfTypeRep) $ Map.elems sigs
    -- we specialcase lists
    cons :: TypeSkeleton -> Set TypeSkeleton
    cons t@(TCons _ r) = Set.insert t $ Set.unions [Set.insert a (cons a) | a <- r]
    cons (TFun arg ret) = Set.insert arg (cons arg <> cons ret)
    cons (TVar _) = Set.empty
    addLi :: TypeSkeleton -> [TypeSkeleton]
    addLi t = t : (addLi' 1 t) -- bump this to get more [A], [[A]],
    -- [[[A]]], etc.
      where
        addLi' :: Int -> TypeSkeleton -> [TypeSkeleton]
        addLi' 0 _ = []
        addLi' n t = t' : (addLi' (n - 1) t')
          where
            t' = TCons "[]" [t]

sigGivens ::
    (TypeSkeleton -> TypeSkeleton) ->
    Sig ->
    (TypeSkeleton -> Maybe Instance) ->
    (Sig, Map TypeSkeleton (Text, Value), Map TypeSkeleton (Text, Func))
sigGivens typeMod sigs instances =
    ( Map.fromList (mapMaybe consName allCons)
    , eq_insts
    , arbs
    )
  where
    user_eq = mapMaybe g_eq $ Map.assocs sigs
      where
        g_eq (k, GivenFun (GivenInst _ eq) tsk) = Just (tsk, (k, eq))
        g_eq _ = Nothing
    eq_insts =
        Map.fromList $
            user_eq
                ++ mapMaybe
                    (\c -> (c,) . fmap sfFunc <$> toEqInst c)
                    (filter isCon allCons)
    user_arbs = mapMaybe g_arb $ Map.assocs sigs
      where
        g_arb (k, f@(GivenFun (GivenVar{}) tsk)) = Just (tsk, (k, f))
        g_arb _ = Nothing
    arbs =
        Map.fromList
            ( user_arbs
                ++ mapMaybe (\ty -> (ty,) <$> consName ty) allCons
            )

    isCon (TCons _ _) = True
    isCon _ = False
    allCons = instanceTypes typeMod sigs
    toEqInst e
        | Just inst <- instances e
        , Just eqf <- inst_eq inst =
            g inst eqf
      where
        g inst eqf =
            Just
                ( "<@Eq_" <> inst_text inst <> "@>"
                , GivenFun (GivenInst (inst_text inst) eqf) $
                    TCons "Eq" [e]
                )
    toEqInst _ = Nothing

    consName :: TypeSkeleton -> Maybe (Text, Func)
    consName t = g <$> instances t
      where
        g inst = toTup (GivenFun (GivenVar (inst_prefix inst) (inst_text inst) 0 (inst_gen inst)) t)
        toTup gf@(GivenFun gv _) = (gvToName gv, gf)

addExplicitEquality :: (Typeable a) => (a -> a -> Bool) -> Sig
addExplicitEquality (fun :: a -> a -> Bool) = Map.singleton key val
  where
    g_tr = typeRep (Proxy :: Proxy a)
    key = "<@Eq_" <> (T.pack $ show g_tr) <> "@>"
    val =
        GivenFun (GivenInst (T.pack (show g_tr)) (toValue fun)) $
            TCons "Eq" [typeRepToTypeSkeleton g_tr]

addEquality :: (Eq a, Typeable a) => Proxy a -> Sig
addEquality (Proxy :: Proxy a) = Map.singleton key val
  where
    g_tr = typeRep (Proxy :: Proxy a)
    key = "<@Eq_" <> (T.pack $ show g_tr) <> "@>"
    val =
        GivenFun (GivenInst (T.pack (show g_tr)) (toValue ((==) :: a -> a -> Bool))) $
            TCons "Eq" [typeRepToTypeSkeleton g_tr]

addArbitrary :: (Typeable a, Arbitrary a) => Proxy a -> Sig
addArbitrary (Proxy :: Proxy a) = Map.singleton (gvToName gv) val
  where
    g_tr = typeRep (Proxy :: Proxy a)
    gv = givenVar g_tr 0 (generator (DynGen (arbitrary :: Gen a)))
    val = GivenFun gv $ typeRepToTypeSkeleton g_tr

genRepFromProxy ::
    (Show a, Eq a, Typeable a, Arbitrary a) =>
    Proxy a -> GeneratedInstance
genRepFromProxy (Proxy :: Proxy a) = Gend{..}
  where
    g_tr = typeRep (Proxy :: Proxy a)
    g_arb = DynGen (arbitrary :: Gen a)
    g_eq = Just (toDyn ((==) :: a -> a -> Bool))
    g_li_i = genRepFromProxy (Proxy :: Proxy [a])

genRepFromProxyNoEq ::
    (Typeable a, Arbitrary a) =>
    Proxy a -> GeneratedInstance
genRepFromProxyNoEq (Proxy :: Proxy a) = Gend{..}
  where
    g_tr = typeRep (Proxy :: Proxy a)
    g_arb = DynGen (arbitrary :: Gen a)
    g_eq = Nothing
    g_li_i = genRepFromProxyNoEq (Proxy :: Proxy [a])

arith :: (Typeable a, Num a, Eq a) => Proxy a -> Sig
arith p =
    Map.fromList $
        ( map (fmap extraFunc) $
            [ ("0", toDyn zero)
            , ("1", toDyn $ 1 `asProxyTypeOf` p)
            ]
        )
  where
    zero = 0 `asProxyTypeOf` p

typeRepToTypeSkeleton :: TypeRep -> TypeSkeleton
typeRepToTypeSkeleton tr
    | tcn == "->"
    , [arg, ret] <- args =
        TFun arg ret
    | otherwise = TCons (T.pack tcn) args
  where
    (tc, tra) = splitTyConApp tr
    tcn = typeConName tc
    args = map typeRepToTypeSkeleton tra

{- | The type skeleton of a type. An extraReps function can use it to
recognize a type: t == typeSkeletonOf (Proxy :: Proxy MyType).
-}
typeSkeletonOf :: (Typeable a) => Proxy a -> TypeSkeleton
typeSkeletonOf = typeRepToTypeSkeleton . typeRep

{- | The name of a type constructor, with its module, so that two types with
the same name in different modules stay apart. GHC 9.6 and later give
some built-in type constructors new names, for example List for []. For
these, the function gives the name of the special syntax.
-}
typeConName :: TyCon -> String
typeConName tc
    | tc == tyConOf (Proxy :: Proxy [()]) = "[]"
    | tc == tyConOf (Proxy :: Proxy ((), ())) = "(,)"
    | tc == tyConOf (Proxy :: Proxy ()) = "()"
    | tc == tyConOf (Proxy :: Proxy (() -> ())) = "->"
    | otherwise = tyConModule tc ++ "." ++ tyConName tc

{- | The types that stand for type variables, with the names of the type
variables.
-}
carriers :: [(TypeSkeleton, Text)]
carriers =
    [ (typeSkeletonOf (Proxy :: Proxy A), "a")
    , (typeSkeletonOf (Proxy :: Proxy B), "b")
    , (typeSkeletonOf (Proxy :: Proxy C), "c")
    , (typeSkeletonOf (Proxy :: Proxy D), "d")
    , (typeSkeletonOf (Proxy :: Proxy Acc), "acc")
    ]

{- | The generators and the equalities of the types that the signatures of
the benchmarks use.
-}
builtinReps :: [(TypeSkeleton, GeneratedInstance)]
builtinReps =
    [ withEq (Proxy :: Proxy A)
    , withEq (Proxy :: Proxy B)
    , withEq (Proxy :: Proxy C)
    , withEq (Proxy :: Proxy D)
    , withEq (Proxy :: Proxy Acc)
    , withEq (Proxy :: Proxy ())
    , withEq (Proxy :: Proxy Int)
    , withEq (Proxy :: Proxy Bool)
    , withEq (Proxy :: Proxy Char)
    , withEq (Proxy :: Proxy Integer)
    , withEq (Proxy :: Proxy Double)
    , withEq (Proxy :: Proxy Float)
    , withEq (Proxy :: Proxy Ordering)
    , withEq (Proxy :: Proxy Word)
    , withoutEq (Proxy :: Proxy (A -> B))
    , withoutEq (Proxy :: Proxy (A -> A))
    , withEq (Proxy :: Proxy (A, B))
    , withEq (Proxy :: Proxy (A, A))
    , withEq (Proxy :: Proxy ([A], [B]))
    , withEq (Proxy :: Proxy ([A], [A]))
    ]
  where
    withEq :: (Show a, Eq a, Typeable a, Arbitrary a) => Proxy a -> (TypeSkeleton, GeneratedInstance)
    withEq p = (typeSkeletonOf p, genRepFromProxy p)
    withoutEq :: (Typeable a, Arbitrary a) => Proxy a -> (TypeSkeleton, GeneratedInstance)
    withoutEq p = (typeSkeletonOf p, genRepFromProxyNoEq p)

-- | The type constructor of a type.
tyConOf :: (Typeable a) => Proxy a -> TyCon
tyConOf = typeRepTyCon . typeRep

type Sig = Map Text Func

-- | A function of the signature, and its type.
data Func
    = SigFunc
        { sf_func :: Value
        , sf_rep :: TypeSkeleton
        }
    | GenFunc
        { gf_func :: Value
        , gf_rep :: TypeSkeleton
        }
    | GivenFun {given_info :: GivenInfo, giv_rep :: TypeSkeleton}
    deriving (Show)

moreGenerators :: Func -> [Func]
moreGenerators (GivenFun (GivenVar prefix ty _ g) grep) =
    map (\v -> GivenFun (GivenVar prefix ty v g) grep) [0 ..]
moreGenerators _ = []

{- | What the search gives a signature: an equality, with the type as
'TypeRep' shows it, or a variable, with the prefix of its name, the type
as 'TypeRep' shows it, its index, and the generator of its values.
-}
data GivenInfo
    = GivenInst Text Value
    | GivenVar Text Text Int Generator
    deriving (Show)

{- | The variable with an index of the type of a 'TypeRep'. The name of a
list variable starts with xs, of a function variable with f, and of any
other variable with x.
-}
givenVar :: TypeRep -> Int -> Generator -> GivenInfo
givenVar tr = GivenVar (namePrefix tr) (T.pack (show tr))

{- | The prefix of the names of the variables of a type: xs for a list, f
for a function, and x for any other type.
-}
namePrefix :: TypeRep -> Text
namePrefix tr = case typeConName (typeRepTyCon tr) of
    "[]" -> "xs"
    "->" -> "f"
    _ -> "x"

gvToNameNoType :: GivenInfo -> Text
gvToNameNoType (GivenVar prefix _ i _) = prefix <> T.pack (show i)
gvToNameNoType _ = error "not a given var!"

gvToName :: GivenInfo -> Text
gvToName gv@(GivenVar _ ty _ _) = gvToNameNoType gv <> "_<" <> ty <> ">"
gvToName _ = error "not a given var!"

-- | A generator of QuickCheck, with the type of its values.
data DynGen where
    DynGen :: forall a. (Typeable a) => Gen a -> DynGen

{- | A value of the search: a 'Dynamic', with its type, or a value without
its type. The front end of Haskell gives typed values. By default the
search makes them untyped once, before its phases (see 'untypedSig'). It
runs a term only when each application fits its argument (see
'termType'), and the values of A, B, C, D, and Acc have the representation
of Int. Thus an application of untyped values needs no test of the types.

With SPECFTACULAR_CHECKED=1, the values stay typed, and an application of
two typed values tests the types: a function takes an argument of its
type, or of another of A to Acc, and any other application raises
'IllTyped'. The golden test runs in this mode too, so that a wrong
application fails a test.
-}
data Value = Typed Dynamic | Untyped Any

instance Show Value where
    show _ = "<value>"

-- | An application of a typed function to a typed argument of another type.
newtype IllTyped = IllTyped String
    deriving (Show)

instance Exception IllTyped

-- | A value as a typed value of the search.
toValue :: (Typeable a) => a -> Value
toValue = Typed . toDyn

-- | A value of the search as a value of its type.
fromValue :: (Typeable a) => Value -> a
fromValue (Typed d) = fromMaybe (throw (IllTyped ("not a value of its type: " ++ show (dynTypeRep d)))) (fromDynamic d)
fromValue (Untyped x) = unsafeCoerce x

{- | Apply a function to an argument. When both are typed, A, B, C, D, and
Acc have the representation of Int, so a function can take an argument of
another of them, and any other difference raises 'IllTyped'. When one of
them is untyped, the application has no test. Two untyped values come
first, as in the search without SPECFTACULAR_CHECKED.
-}
apply :: Value -> Value -> Value
apply (Untyped f) (Untyped x) = Untyped ((unsafeCoerce f :: Any -> Any) x)
apply (Typed df@(Dynamic (TR.Fun ta tr) f)) (Typed dx@(Dynamic tx x)) =
    case dynApply df dx of
        Just r -> Typed r
        Nothing
            | sameUpToCarriers (typeRepToTypeSkeleton (TR.SomeTypeRep ta)) (typeRepToTypeSkeleton (TR.SomeTypeRep tx)) ->
                Typed (Dynamic (unsafeCoerce tr) (unsafeCoerce f x))
            | otherwise -> illTyped df dx
apply (Typed df) (Typed dx) = illTyped df dx
apply f x = Untyped ((unsafeCoerce (rawValue f) :: Any -> Any) (rawValue x))

-- | The representation of a value, without its type.
rawValue :: Value -> Any
rawValue (Typed (Dynamic _ x)) = unsafeCoerce x
rawValue (Untyped x) = x

-- | The value without its type.
untyped :: Value -> Value
untyped = Untyped . rawValue

-- | The error of an application of two values whose types do not fit.
illTyped :: Dynamic -> Dynamic -> a
illTyped df dx = throw (IllTyped ("cannot apply " ++ show (dynTypeRep df) ++ " to " ++ show (dynTypeRep dx)))

-- | The value of a 'Dynamic'.
dynamicValue :: Dynamic -> Value
dynamicValue = Typed

-- | A generator of the values of a type: the value of a seed and a size.
newtype Generator = Generator (Int -> Int -> Value)

instance Show Generator where
    show _ = "<generator>"

{- | The generator of a generator of QuickCheck: unGen with the seed through
mkQCGen.
-}
generator :: DynGen -> Generator
generator (DynGen g) = Generator (\seed size -> toValue (unGen g (mkQCGen seed) size))

-- ConFunc comes from the user provided signature, and we want at least
-- one of these to show up.
conFunc :: Dynamic -> Func
conFunc f = SigFunc{sf_func = dynamicValue f, sf_rep = typeRepToTypeSkeleton (dynTypeRep f)}

-- extraFuncs are from generators like arith, but we don't *require* them,
-- they're just extra.
extraFunc :: Dynamic -> Func
extraFunc f = GenFunc{gf_func = dynamicValue f, gf_rep = typeRepToTypeSkeleton (dynTypeRep f)}

sfFunc :: Func -> Value
sfFunc (SigFunc{..}) = sf_func
sfFunc (GenFunc{..}) = gf_func
-- Should not happen
sfFunc (GivenFun{given_info = GivenInst _ inst_f}) = inst_f
sfFunc (GivenFun{}) = toValue ()

sfTypeRep :: Func -> TypeSkeleton
sfTypeRep (SigFunc{..}) = sf_rep
sfTypeRep (GenFunc{..}) = gf_rep
sfTypeRep (GivenFun{..}) = giv_rep

con :: (Typeable a) => Text -> a -> Sig
con name fun = Map.singleton name $ (conFunc $ toDyn fun)

extra :: (Typeable a) => Text -> a -> Sig
extra name fun = Map.singleton name $ (extraFunc $ toDyn fun)

type VarVals = Map Text Value

generalizeType :: TypeSkeleton -> TypeSkeleton
generalizeType t | Just v <- lookup t carriers = TVar v
generalizeType (TCons s r) = TCons s $ map generalizeType r
generalizeType (TFun arg ret) = TFun (generalizeType arg) (generalizeType ret)
generalizeType tsk = tsk

monomorphiseType :: TypeSkeleton -> TypeSkeleton
monomorphiseType t | Just _ <- lookup t carriers = typeSkeletonOf (Proxy :: Proxy A)
monomorphiseType (TCons s r) = TCons s $ map monomorphiseType r
monomorphiseType (TFun arg ret) = TFun (monomorphiseType arg) (monomorphiseType ret)
monomorphiseType tsk = tsk

{- | The template of a term: each variable becomes a template variable of
the same type. Equal variables give equal template variables.
-}
toTemplate :: Sig -> Term -> Term
toTemplate sig (Term "app" [ty, f, x]) = Term "app" [templateType ty, toTemplate sig f, toTemplate sig x]
toTemplate sig (Term (Symbol s) [ty]) =
    Term (Symbol name) [templateType ty]
  where
    name = case sig Map.!? s of
        Just (GivenFun{given_info = GivenVar{}}) -> "<v>" <> s
        _ -> s
toTemplate _ t = t

-- | Abstract carrier types in a rule share one type substitution.
templateType :: Term -> Term
templateType t
    | Just v <- lookup t [(typeSkeletonToTerm ty, name) | (ty,name) <- carriers] = Term (Symbol ("<t>" <> v)) []
templateType (Term s ts) = Term s (map templateType ts)

-- | Whether two types are equal when A, B, C, D, and Acc are one type.
sameUpToCarriers :: TypeSkeleton -> TypeSkeleton -> Bool
sameUpToCarriers a b | isCarrier a && isCarrier b = True
  where
    isCarrier t = t `elem` map fst carriers
sameUpToCarriers (TCons ca as) (TCons cb bs) =
    ca == cb && length as == length bs && and (zipWith sameUpToCarriers as bs)
sameUpToCarriers (TFun a r) (TFun b s) = sameUpToCarriers a b && sameUpToCarriers r s
sameUpToCarriers a b = a == b

-- | The type annotation of a term. Resolve enumeration holes at carrier A.
annotationType :: Term -> Either String TypeSkeleton
annotationType (Term "->" [Term "(->)" [], a, b]) = TFun <$> annotationType a <*> annotationType b
annotationType (Term "Mu" []) = Right (typeSkeletonOf (Proxy :: Proxy A))
annotationType (Term s [])
    | Just t <- lookup s (zip ["var1", "var2", "var3", "var4", "acc"] (map fst carriers)) = Right t
annotationType (Term (Symbol s) ts) = TCons s <$> traverse annotationType ts

-- | The canonical annotation of a type.
typeSkeletonToTerm :: TypeSkeleton -> Term
typeSkeletonToTerm (TCons s args) = Term (Symbol s) (map typeSkeletonToTerm args)
typeSkeletonToTerm (TFun a b) = Term "->" [Term "(->)" [], typeSkeletonToTerm a, typeSkeletonToTerm b]
typeSkeletonToTerm (TVar v) = Term (Symbol v) []

-- | Canonical type annotations, before comparison across search phases.
canonicalTypes :: Term -> Term
canonicalTypes (Term "app" [ty, f, x]) = Term "app" [canonicalType ty, canonicalTypes f, canonicalTypes x]
canonicalTypes (Term s [ty]) = Term s [canonicalType ty]
canonicalTypes t = t

-- | Resolve an annotation without changing the program symbols.
canonicalType :: Term -> Term
canonicalType = either (error . ("invalid type annotation: " ++)) typeSkeletonToTerm . annotationType

{- | Match a signature type against one occurrence. Each carrier has one
consistent instance in that occurrence. Concrete type constructors stay fixed.
-}
matchType :: TypeSkeleton -> TypeSkeleton -> Either String (Map Text TypeSkeleton)
matchType patternType actualType = go (generalizeType patternType) actualType Map.empty
  where
    go (TVar v) t s = case Map.lookup v s of
        Nothing -> Right (Map.insert v t s)
        Just t' | t == t' -> Right s
        _ -> Left "inconsistent type instance"
    go (TFun a b) (TFun c d) s = go a c s >>= go b d
    go (TCons c as) (TCons d bs) s
        | c == d && length as == length bs = foldM (\m (a,b) -> go a b m) s (zip as bs)
    go _ _ _ = Left "signature does not match its type annotation"

{- | Check every leaf and application against its annotation. Signature
constants are parametric at A to Acc. Generated variables and equalities
keep their declared types.
-}
termType :: Sig -> Term -> Either String TypeSkeleton
termType sig (Term "app" [ty, f, x]) = do
    tf <- termType sig f
    tx <- termType sig x
    tr <- annotationType ty
    case tf of
        TFun ta tb | ta == tx && tb == tr -> Right tr
        _ -> Left ("cannot apply " ++ show tf ++ " to " ++ show tx ++ " at " ++ show tr)
termType sig (Term (Symbol sym) annotations) = do
    fun <- maybe (Left ("no symbol " ++ T.unpack sym)) Right (Map.lookup sym sig)
    ty <- case annotations of
        [annotation] -> annotationType annotation
        [] -> Right (sfTypeRep fun)
        _ -> Left "invalid leaf annotation"
    case fun of
        GivenFun{} | ty /= sfTypeRep fun -> Left "a generated value cannot change its type"
        GivenFun{} -> Right ty
        _ -> ty <$ matchType (sfTypeRep fun) ty

{- | Compile an evaluator once per term. A specialised constant keeps its
verified type in checked mode. Each application still uses 'apply'.
-}
compileTerm :: Sig -> Term -> Either String (VarVals -> Value)
compileTerm sig term = termType sig term >> go term
  where
    go (Term "app" [_, f, x]) = do
        fun <- go f
        arg <- go x
        Right (\tc -> apply (fun tc) (arg tc))
    go (Term (Symbol sym) annotations) = case sig Map.!? sym of
        Just (GivenFun{given_info = GivenVar{}}) -> Right (Map.! sym)
        Just (GivenFun{given_info = GivenInst _ inst}) -> Right (const inst)
        Just fun -> do
            ty <- case annotations of
                [annotation] -> annotationType annotation
                _ -> Right (sfTypeRep fun)
            val <- specialiseValue sig fun ty
            Right (const val)
        Nothing -> Left ("no symbol " ++ T.unpack sym)

-- | The value of a checked term on one test case.
evalTerm :: Sig -> VarVals -> Term -> Value
evalTerm sig tc term = either (throw . IllTyped) ($ tc) (compileTerm sig term)

{- | Instantiate a parametric signature constant. A to Acc must denote
abstract type variables. A constant must not inspect their representation
or capture class dictionaries for them. This contract permits the payload
cast after the structural type and kind checks. Generated values do not
pass through this function.
-}
specialiseValue :: Sig -> Func -> TypeSkeleton -> Either String Value
specialiseValue sig fun target
    | target == sfTypeRep fun = Right (sfFunc fun)
    | otherwise = case sfFunc fun of
        Untyped value -> Right (Untyped value)
        Typed dynamic -> do
            bindings <- matchType (sfTypeRep fun) target
            substitution <- Map.fromList <$> traverse (\(t,v) -> (,) <$> representation t <*> representation (bindings Map.! v)) [(t,v) | (t,v) <- carriers, Map.member v bindings]
            specialized <- specialiseDynamic substitution dynamic
            if typeRepToTypeSkeleton (dynTypeRep specialized) == target
                then Right (Typed specialized)
                else Left "specialised constant has the wrong type"
  where
    representation (TFun a b) = do
        a' <- representation a
        b' <- representation b
        functionType a' b'
    representation (TCons name args) = do
        constructor <- maybe (Left ("no type representation for " ++ T.unpack name)) Right (Map.lookup name constructors <|> Map.lookup name generatedConstructors)
        foldM (\f a -> representation a >>= applyType f) constructor args
    representation (TVar _) = Left "unresolved type variable"
    constructors = Map.fromList (concatMap collect (map (g_tr . snd) builtinReps ++ [dynTypeRep d | f <- Map.elems sig, Typed d <- [sfFunc f]]))
    -- A native generator stores its TypeRep without forcing the generated
    -- payload. Consult these types only when the signature lacks a type.
    generatedConstructors = Map.fromList (concatMap collect [dynTypeRep d | GivenFun (GivenVar _ _ _ (Generator g)) _ <- Map.elems sig, Typed d <- [g 0 0]])
    collect (TR.SomeTypeRep rep) = case rep of
        TR.Fun a b -> collect (TR.SomeTypeRep a) ++ collect (TR.SomeTypeRep b)
        TR.App f x -> collect (TR.SomeTypeRep f) ++ collect (TR.SomeTypeRep x)
        _ -> [(T.pack (typeConName (TR.typeRepTyCon rep)), TR.SomeTypeRep rep)]

{- | A signature with untyped values (see 'Value'): its functions, its
equalities, and the values of its generators.
-}
untypedSig :: Sig -> Sig
untypedSig = fmap untypedFunc
  where
    untypedFunc f@(SigFunc{sf_func = v}) = f{sf_func = untyped v}
    untypedFunc f@(GenFunc{gf_func = v}) = f{gf_func = untyped v}
    untypedFunc (GivenFun (GivenInst t v) r) = GivenFun (GivenInst t (untyped v)) r
    untypedFunc (GivenFun (GivenVar p t i g) r) = GivenFun (GivenVar p t i (untypedGenerator g)) r

-- | An instance with untyped values.
untypedInstance :: Instance -> Instance
untypedInstance inst = inst{inst_gen = untypedGenerator (inst_gen inst), inst_eq = untyped <$> inst_eq inst}

-- | A generator of untyped values.
untypedGenerator :: Generator -> Generator
untypedGenerator (Generator g) = Generator (\seed size -> untyped (g seed size))

{- | The test cases of a signature. Keep the n random cases unchanged.
Add eight random cases with separate seeds. Add 32 cases that combine
Int boundaries with empty and singleton lists. Each variable has the same
values in each phase.
-}
testCases :: Int -> Sig -> [VarVals]
testCases n sig = randomCases ++ validationCases ++ boundaryCases
  where
    variables =
        [(v, i, g, t) | (v, GivenFun (GivenVar _ _ i g) t) <- Map.assocs sig]
    randomCases =
        [ Map.fromList [(v, generate g (hash (k, v)) size) | (v, _, g, _) <- variables]
        | (k, size) <- zip [0 :: Int ..] (testSizes n)
        ]
    validationCases =
        [ Map.fromList
            [(v, generate g (hash ("validation" :: String, k, v)) size) | (v, _, g, _) <- variables]
        | (k, size) <- zip [0 :: Int ..] (testSizes 8)
        ]
    boundaryCases =
        [ Map.fromList
            [ ( v
              , fromMaybe
                    (generate g (hash ("boundary" :: String, k, active, v)) 100)
                    (lookup t (if i `mod` 4 == active then nonempty else empty))
              )
            | (v, i, g, t) <- variables
            ]
        | (k, boundary) <- zip [0 :: Int ..] [minBound, minBound + 1, -1, 0, 1, 2, maxBound - 1, maxBound]
        , let empty = boundaryValues boundary False
        , let nonempty = boundaryValues boundary True
        , active <- [0 .. 3]
        ]
    generate (Generator g) seed size = g seed size

{- | Values for Int and the carrier types, and their first three list
types. A selected list contains one zero value. Every other list is empty.
Each value keeps its exact Haskell type. Other types use their generators.
-}
boundaryValues :: Int -> Bool -> [(TypeSkeleton, Value)]
boundaryValues boundary nonempty =
    [ entry boundary
    , entry (A boundary)
    , entry (B boundary)
    , entry (C boundary)
    , entry (D boundary)
    , entry (Acc boundary)
    ]
        ++ concat [lists (0 :: Int), lists (A 0), lists (B 0), lists (C 0), lists (D 0), lists (Acc 0)]
  where
    entry :: (Typeable a) => a -> (TypeSkeleton, Value)
    entry value = (typeRepToTypeSkeleton (typeOf value), toValue value)
    lists :: (Typeable a) => a -> [(TypeSkeleton, Value)]
    lists value = [entry (pick value), entry (pick (pick value)), entry (pick (pick (pick value)))]
    pick :: a -> [a]
    pick value = [value | nonempty]

{- | The sizes of n test cases, as QuickSpec chooses them (run in
QuickSpec.Internal.Testing.QuickCheck of quickspec-2.2.2). 1% of the test
cases have the size 0. The others are biased towards small sizes: the
size is the maximum size 100 minus the cube root of a number that is
spread evenly over [0, 100^3).
-}
testSizes :: Int -> [Int]
testSizes n =
    replicate zeroes 0
        ++ reverse [maxSize - truncate (fromIntegral u ** (1 / 3) :: Double) | u <- uniform others (maxSize ^ (3 :: Int))]
  where
    others = ceiling (fromIntegral n * (1 - 0.01 :: Double))
    zeroes = n - others
    maxSize = 100
    -- m numbers spread evenly over [0, k), as uniform in QuickSpec.
    uniform m k =
        concat [replicate (m `div` k) i | i <- [0 .. k - 1]]
            ++ [i * k `div` (m `mod` k) | i <- [0 .. m `mod` k - 1]]

{- | Whether two values are equal by an equality. Untyped values compare
without the tests of 'apply'.
-}
equalBy :: Value -> Value -> Value -> Bool
equalBy (Untyped eq) (Untyped a) (Untyped b) = (unsafeCoerce eq :: Any -> Any -> Bool) a b
equalBy eq a b = fromValue (apply (apply eq a) b)

{- | Whether two values are equal, by the equality of their type. Nothing
means that the comparison threw an exception.
-}
valuesEqual :: Value -> Value -> Value -> IO (Maybe Bool)
valuesEqual eq a b = do
    r <- try (evaluate (equalBy eq a b))
    case r of
        Left (e :: SomeException)
            | Just (illTyped :: IllTyped) <- fromException e -> throwIO illTyped
            | otherwise -> return Nothing
        Right x -> return (Just x)

-- TODO: can we kill a branch once a rewriteable term is detected?
--
