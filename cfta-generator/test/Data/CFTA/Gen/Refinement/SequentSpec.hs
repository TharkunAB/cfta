{-# LANGUAGE OverloadedStrings #-}

{- | The geometric sequents of a theory of integer lists as the terms of one
signature with binders: read, write, the counts by size, and the ranks.
-}
module Data.CFTA.Gen.Refinement.SequentSpec (spec) where

import qualified Data.Set as Set
import Test.Hspec (Spec, describe, it, shouldBe)

import Data.CFTA.Formula (Formula (..), Name (..), Relation (..), Sort (..), Term (..))
import Data.CFTA.Gen.ManySorted (SignatureError (..), TypeError (..))
import Data.CFTA.Gen.ManySorted.Scoped (ScopeError (..), scopedAutomaton, scopedTypeCheck)
import Data.CFTA.Gen.Refinement.Sequent
import Data.CFTA.Index (Cardinality (..), ClassRank (..), Size (..))
import Data.CFTA.Path (ChildIndex (..), path)
import Data.CFTA.Refinement.Sequent (Sequent (..), Shape (..), sequent, sequentFormula, shape)
import Data.CFTA.Refinement.Theory
import Data.CFTA.Sized (countOfSize, rankOfSize, sized, termsOfSize, unrankOfSize)
import qualified Data.CFTA.Term as Tree

-- | The sort of integer lists.
list :: Sort
list = NamedSort "List" [IntSort]

-- | The sort of streams. It has no value.
stream :: Sort
stream = NamedSort "Stream" []

{- | Integer lists with the predicate @member@, and streams. Each stream has
another stream in it, so the sort of streams has no value.
-}
lists :: Theory
lists = either (error . show) id (theory [lists', streams] [("member", member)])
  where
    lists' = Datatype list [Constructor "nil" [], Constructor "cons" [("item", IntSort), ("rest", list)]]
    streams = Datatype stream [Constructor "step" [("now", IntSort), ("later", stream)]]
    -- The value occurs in the list when it is the first item, or a member of the rest.
    member =
        PredicateDefinition [("value", IntSort), ("items", list)] $
            Split
                "items"
                [ Branch "nil" [] (Expression Bottom)
                , Branch "cons" ["first", "others"] $
                    Expression (Or [Atom Eq (Var "value") (Var "first"), Predicate "member" [Var "value", Var "others"]])
                ]

-- | Equality at both sorts, the literal 0, binders at both sorts, and at most three binders.
settings :: SequentSettings
settings =
    SequentSettings
        { sequentRelations = [(IntSort, [Eq]), (list, [Eq])]
        , sequentLiterals = [0]
        , sequentBinderSorts = [IntSort, list]
        , sequentBinders = 3
        }

-- | The largest size that the spec lists.
largest :: Integer
largest = 15

-- | The terms of each size from 1 to 'largest' for the theory 'lists' with the settings.
termsBySize :: SequentSettings -> [(Integer, [Tree.Term SequentSymbol])]
termsBySize current = [(size, termsOfSize classes (Size size)) | size <- [1 .. largest]]
  where
    automaton = either (error . show) id (scopedAutomaton sequentCodec (sequentSignature lists current))
    classes = either (error . show) id (sized automaton)

-- | The empty list.
nil :: Term
nil = App "nil" []

-- | The sequent with the prefix @bound_@ on each bound name, so its names are not the names of 'readSequent'.
renamed :: Sequent -> Sequent
renamed (Sequent bound body heads) = Sequent (map binder bound) (map atom body) [(map binder binders, map atom parts) | (binders, parts) <- heads]
  where
    rename (Name text) = Name ("bound_" <> text)
    binder (name, sort) = (rename name, sort)
    atom (Atom relation left right) = Atom relation (term left) (term right)
    atom (Predicate name arguments) = Predicate name (map term arguments)
    atom other = other
    term (Var name) = Var (rename name)
    term (App name arguments) = App name (map term arguments)
    term other = other

spec :: Spec
spec = describe "Data.CFTA.Gen.Refinement.Sequent" $ do
    let signature = sequentSignature lists settings
        automaton = either (error . show) id (scopedAutomaton sequentCodec signature)
        classes = either (error . show) id (sized automaton)
        bySize = termsBySize settings
        terms = concatMap snd bySize
        reads' = [(term, readSequent term) | term <- terms]
        sequents = [s | (_, Just s) <- reads']
        write = writeSequent signature

    it "reads each term as a well-sorted sequent that the formula gives again" $ do
        [term | (term, Nothing) <- reads'] `shouldBe` []
        [term | term <- terms, scopedTypeCheck sequentCodec signature term /= Right RootSort] `shouldBe` []
        [s | s <- sequents, sequent (sequentFormula s) /= Right s] `shouldBe` []

    it "reads distinct terms as distinct sequents" $
        Set.size (Set.fromList [(sequentBound s, sequentBody s, sequentHead s) | s <- sequents]) `shouldBe` length terms

    it "writes the term of a sequent that it reads" $
        [term | (term, Just s) <- reads', write s /= Right term] `shouldBe` []

    it "reads the sequent of a written sequent, up to the names of the binders" $ do
        [s | s <- sequents, fmap readSequent (write (renamed s)) /= Right (Just s)] `shouldBe` []
        let cases =
                Sequent
                    [("xs", list)]
                    []
                    [([], [Atom Eq (Var "xs") nil]), ([("h", IntSort), ("t", list)], [Atom Eq (Var "xs") (App "cons" [Var "h", Var "t"])])]
        fmap readSequent (write cases)
            `shouldBe` Right
                ( Just $
                    Sequent
                        [("x0", list)]
                        []
                        [ ([], [Atom Eq (Var "x0") nil])
                        , ([("x1", IntSort), ("x2", list)], [Atom Eq (Var "x0") (App "cons" [Var "x1", Var "x2"])])
                        ]
                )
        -- A variable refers to the innermost binder of its name.
        fmap readSequent (write (Sequent [("a", IntSort), ("a", IntSort)] [] [([], [Atom Eq (Var "a") (Lit 0)])]))
            `shouldBe` Right (Just (Sequent [("x0", IntSort), ("x1", IntSort)] [] [([], [Atom Eq (Var "x1") (Lit 0)])]))

    {- The first sizes. Size 3 is true ==> false. Each universal binder adds
    one, at the sort Int or List: 2 at size 4, 4 at size 5, and 8 at size 6.
    The bound stops at three binders. Size 7 has one atom without variables
    in the body: 0 == 0, nil == nil, or member(0, nil). The first sequents
    that are not Horn clauses have the size 10: exists x0. a, where a is one
    of the 7 atoms of size 3 with x0 at the sort Int, or one of the 7 atoms
    with x0 at the sort List. -}
    it "counts the sequents and the Horn clauses of each size" $ do
        let counts = [count | size <- [1 .. largest], let Cardinality count = countOfSize classes (Size size)]
        counts `shouldBe` [0, 0, 1, 2, 4, 8, 3, 14, 56, 202, 250, 1122, 1135, 6136, 6392]
        [toInteger (length members) | (_, members) <- bySize] `shouldBe` counts
        [length [() | Just s <- map readSequent members, shape s == Horn] | (_, members) <- bySize]
            `shouldBe` [0, 0, 1, 2, 4, 8, 3, 14, 56, 188, 150, 636, 958, 4874, 3563]

    it "ranks and unranks the terms of each size" $ do
        [ term
          | (size, members) <- bySize
          , (rank, term) <- zip [0 ..] members
          , rankOfSize classes term /= Just (Size size, ClassRank rank)
          ]
            `shouldBe` []
        [ term
          | (size, members) <- bySize
          , (rank, term) <- zip [0 ..] members
          , unrankOfSize classes (Size size) (ClassRank rank) /= Just term
          ]
            `shouldBe` []

    it "refuses an ill-sorted sequent" $ do
        write (Sequent [("n", IntSort)] [] [([], [Atom Eq (Var "n") nil])])
            `shouldBe` Left
                ( IllTyped $
                    WrongChildSort
                        (path (map ChildIndex [0, 1, 0, 0]))
                        (Comparison Eq IntSort)
                        [TermSort IntSort, TermSort IntSort]
                        [Just (TermSort IntSort), Just (TermSort list)]
                )
        write (Sequent [("s", stream)] [] []) `shouldBe` Left (IllTyped (UnknownFunction (path []) (Universal stream)))
        write (Sequent [("n", IntSort)] [Atom Lt (Var "n") (Lit 0)] [])
            `shouldBe` Left (IllTyped (UnknownFunction (path (map ChildIndex [0, 0, 0])) (Comparison Lt IntSort)))

    it "refuses a symbol that the input does not have" $ do
        write (Sequent [("xs", list)] [] [([], [Atom Eq (App "length" [Var "xs"]) (Lit 0)])])
            `shouldBe` Left (UnknownName "length")
        write (Sequent [("xs", list)] [Predicate "sorted" [Var "xs"]] []) `shouldBe` Left (UnknownName "sorted")
        write (Sequent [("n", IntSort)] [] [([], [Atom Eq (App "step" [Var "n", Var "n"]) (App "step" [Var "n", Var "n"])])])
            `shouldBe` Left (UnknownName "step")
        write (Sequent [] [] [([], [Atom Eq (Lit 7) (Lit 7)])])
            `shouldBe` Left (IllTyped (UnknownFunction (path (map ChildIndex [1, 0, 0, 0])) (Literal 7)))

    it "refuses a sequent outside the form of the grammar or the bound" $ do
        write (Sequent [] [] [([], [Atom Eq (Var "n") (Lit 0)])]) `shouldBe` Left (FreeName "n")
        write (Sequent [] [] [([("n", IntSort)], [])]) `shouldBe` Left EmptyDisjunct
        write (Sequent [] [Or [Atom Eq (Lit 0) (Lit 0)]] []) `shouldBe` Left (NotAnAtom (Or [Atom Eq (Lit 0) (Lit 0)]))
        write (Sequent [] [Atom Eq (Add (Lit 0) (Lit 0)) (Lit 0)] []) `shouldBe` Left (NotATerm (Add (Lit 0) (Lit 0)))
        write (Sequent (replicate 4 ("n", IntSort)) [] [])
            `shouldBe` Left (IllTyped (TooManyBinders (path (map ChildIndex [0, 0, 0])) (Universal IntSort)))

    it "gives a binder only a sort of the settings" $ do
        let listBinders = settings{sequentBinderSorts = [list]}
            restricted = termsBySize listBinders
            otherSort symbol = case symbol of
                Universal sort -> sort /= list
                Existential sort -> sort /= list
                _ -> False
        [toInteger (length members) | (_, members) <- restricted]
            `shouldBe` [0, 0, 1, 1, 1, 1, 3, 7, 19, 45, 76, 203, 307, 991, 1597]
        [term | (_, members) <- restricted, term <- members, any otherSort term] `shouldBe` []
        restricted `shouldBe` [(size, filter (not . any otherSort) members) | (size, members) <- bySize]
        writeSequent (sequentSignature lists listBinders) (Sequent [("n", IntSort)] [] [])
            `shouldBe` Left (IllTyped (UnknownFunction (path []) (Universal IntSort)))

    it "gives only sequents without variables for an empty list of binder sorts" $ do
        let closed = termsBySize settings{sequentBinderSorts = []}
            binds s = not (null (sequentBound s) && all (null . fst) (sequentHead s))
        [toInteger (length members) | (_, members) <- closed] `shouldBe` [0, 0, 1, 0, 0, 0, 3, 0, 6, 0, 16, 0, 45, 0, 116]
        [term | (_, members) <- closed, term <- members, maybe True binds (readSequent term)] `shouldBe` []

    it "refuses settings that repeat a symbol or name a sort outside the signature" $ do
        let rejection current = either Just (const Nothing) (scopedAutomaton sequentCodec (sequentSignature lists current))
        rejection settings{sequentLiterals = [0, 0]} `shouldBe` Just (BaseError (DuplicateSymbol (Literal 0)))
        rejection settings{sequentRelations = [(stream, [Eq])]} `shouldBe` Just (BaseError (UnknownSort (TermSort stream)))
        rejection settings{sequentBinderSorts = [stream]} `shouldBe` Just (BaseError (UnknownSort (TermSort stream)))
        rejection settings{sequentBinderSorts = [list, list]} `shouldBe` Just (BaseError (DuplicateSymbol (Universal list)))
