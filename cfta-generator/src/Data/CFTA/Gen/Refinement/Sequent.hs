{- | The geometric sequents over the symbols of a theory, as the terms of one
signature with binders.

'sequentSignature' gives the signature, and 'sequentCodec' gives its codec.
'Data.CFTA.Gen.ManySorted.Scoped.scopedAutomaton' gives the automaton of the
signature, and "Data.CFTA.Sized" counts, lists, ranks, and unranks its terms
by size. 'Data.CFTA.Gen.ManySorted.Scoped.scopedTypeCheck' checks one term.
'readSequent' gives the 'Sequent' of a term, and 'writeSequent' gives the
term of a 'Sequent'. See Note [Sequents as terms].
-}
module Data.CFTA.Gen.Refinement.Sequent (
    SequentSettings (..),
    SequentSort (..),
    SequentSymbol (..),
    WriteError (..),
    sequentSignature,
    sequentCodec,
    readSequent,
    writeSequent,
) where

import Data.Bifunctor (first)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as Text

import Data.CFTA.Formula (Formula (..), Name (..), Relation, Sort (..))
import qualified Data.CFTA.Formula as Formula
import Data.CFTA.Gen.ManySorted (SortedFunction (..), SortedSignature (..), TypeError)
import Data.CFTA.Gen.ManySorted.Scoped (Binding (..), ScopedCodec (..), ScopedSignature (..), scopedTypeCheck)
import Data.CFTA.Refinement.Sequent (Sequent (..))
import Data.CFTA.Refinement.Theory (
    Datatype (..),
    Theory,
    TheoryDefinition (..),
    inhabitedDatatypes,
    theoryDatatypes,
    theoryDeclarations,
    theoryDefinitions,
 )
import Data.CFTA.Term (Term (Node))

{- Note [Sequents as terms]
~~~~~~~~~~~~~~~~~~~~~~~~~~~
A geometric sequent over the symbols of a theory is a term of a signature
with binders ("Data.CFTA.Gen.ManySorted.Scoped"). The quantifiers are the
binders, and a variable is a de Bruijn index. Thus the well-sorted sequents
of a theory are the language of one automaton. "Data.CFTA.Sized" counts,
lists, ranks, and unranks them by size, and the ranks are the same in each
process.

The grammar has these sorts and symbols:

    sequent   ::= Universal s (sequent) | Implication (atoms, head)
    atoms     ::= AtomsEnd | AtomsCons (atom, atoms)
    head      ::= HeadEnd | HeadCons (disjunct, head)
    disjunct  ::= Existential s (disjunct) | Disjunct (atom, atoms)
    atom      ::= Comparison r s (term s, term s) | PredicateAtom p (term s1, ..., term sk)
    term s    ::= Application f (term s1, ..., term sk) | Literal n | Variable i

The symbols 'Universal' and 'Existential' bind one variable of the sort s in
their child. The universal binders are only at the root, and the existential
binders are only at the root of a disjunct. A disjunct has at least one atom.
Thus each term is a sequent of the geometric form. Each geometric sequent over
the symbols has a term, in the limits below.

The design has these reasons:

  * A sorted signature gives each symbol one list of argument sorts, and a
    'Binding' gives each symbol one list of scopes. Thus a comparison and a
    binder have one symbol for each sort.
  * An integer literal is a symbol without children, one for each literal of
    the settings. The automaton has one leaf for all values of a value sort,
    so the count of a size would count all the literals as one term.
  * A predicate and a function have different symbols, so 'readSequent' needs
    no theory.
  * The sorts are 'IntSort' and the datatypes of the theory that have a
    value ('Data.CFTA.Refinement.Theory.inhabitedDatatypes'). A universal
    binder of a sort without a value gives a sequent that is always true. The
    signature has no constructor, function, or predicate with a sort outside
    this list.
  * 'writeSequent' gives a comparison the sort of its left term. Then
    'scopedTypeCheck' decides whether the term is in the language. Thus the
    sorts, the literals, the comparisons, the binder sorts, and the bound need
    no other check.
  * 'readSequent' gives the name x0 to the outermost binder, x1 to the binder
    in it, and so on: the number is the number of binders around the binder.
    Along one path from the root, two binders have different numbers. Thus
    reading is injective, and 'writeSequent' gives the term again. Two
    disjuncts can bind the same name, because their scopes do not overlap.
    'Data.CFTA.Refinement.Sequent.sequent' accepts this.

The language has these limits:

  * Each order of the atoms of a list is a different term, and the same atom
    can occur twice. The same is true for the disjuncts of a head, and for the
    order of binders of different sorts. A comparison and its reverse, such as
    @a < b@ and @b > a@, are different terms.
  * The language holds sequents with a binder that no atom uses.
  * A binder has a sort of 'sequentBinderSorts'. Each of these sorts must be
    a sort of the signature: 'IntSort' or a datatype with a value. For
    another sort, 'Data.CFTA.Gen.ManySorted.Scoped.scopedAutomaton' gives
    'UnknownSort'. A sort without a constructor has no value, so it is not a
    sort of the signature. An empty list gives no binder, so the language then
    holds only the sequents without variables. The terms keep all the sorts
    of the signature.
  * A disjunct without atoms is not in the language, but
    'Data.CFTA.Refinement.Sequent.sequent' gives one for a 'Top' part of a
    head. 'writeSequent' refuses it with 'EmptyDisjunct'.
  * A bound name is a 'Formula.Var'. 'writeSequent' reads a 'Formula.App'
    without arguments as a constructor or a function, also when a binder has
    its name, and refuses an unknown name with 'UnknownName'.
  * A term is a variable, a literal, or the application of a constructor or a
    function of the theory. The arithmetic of 'Data.CFTA.Formula.Term', such as
    'Formula.Add', is not in the language. 'Formula.Ite' and 'Formula.Cast' are
    not in the language.
  * The bound applies to each position: the universal binders, and the
    existential binders of the disjunct around the position. A state of the
    automaton is an environment and a sort, so the number of states increases
    exponentially with the bound.
  * A name of 'readSequent', such as x0, can also be the name of a constructor
    or a function of the theory. The sequent is still exact, because a variable
    is a 'Formula.Var' and an application is a 'Formula.App'. But the text of
    the sequent then has one name for two things.
  * 'writeSequent' accepts a binder that hides an earlier binder of the same
    name. A variable then refers to the innermost binder of its name.
  * The size of a term counts the binders and the ends of the lists. The
    smallest sequent, @true ==> false@, has the size 3.
-}

-- | What a sequent can use in addition to the symbols of a theory. See Note [Sequents as terms].
data SequentSettings = SequentSettings
    { sequentRelations :: ![(Sort, [Relation])]
    -- ^ The comparisons at each sort. The two terms of a comparison have that sort.
    , sequentLiterals :: ![Integer]
    -- ^ The integer literals.
    , sequentBinderSorts :: ![Sort]
    {- ^ The sorts that a universal or an existential binder can have. Each
    sort must be a sort of the signature. An empty list gives no binder.
    -}
    , sequentBinders :: !Int
    {- ^ The number of binders around each position, at most: the universal
    binders, and the existential binders of the disjunct around the position.
    -}
    }
    deriving (Eq, Show)

-- | A sort of the grammar of sequents.
data SequentSort
    = -- | The terms of a sort of the theory.
      TermSort !Sort
    | -- | One atom: a comparison or a predicate.
      AtomSort
    | -- | A list of atoms.
      AtomsSort
    | -- | One disjunct of a head: existential binders, then a non-empty list of atoms.
      DisjunctSort
    | -- | A list of disjuncts: the head of a sequent.
      HeadSort
    | -- | A sequent below some or all of its universal binders. It is the root sort.
      RootSort
    deriving (Eq, Ord, Show)

-- | A symbol of the grammar of sequents.
data SequentSymbol
    = -- | A universal binder of one variable of the sort, around the rest of the sequent.
      Universal !Sort
    | -- | The body and the head of a sequent.
      Implication
    | -- | The end of a list of atoms.
      AtomsEnd
    | -- | An atom, and the rest of a list of atoms.
      AtomsCons
    | -- | The end of a list of disjuncts.
      HeadEnd
    | -- | A disjunct, and the rest of a list of disjuncts.
      HeadCons
    | -- | An existential binder of one variable of the sort, around the rest of a disjunct.
      Existential !Sort
    | -- | The first atom of a disjunct, and the list of its other atoms.
      Disjunct
    | -- | A comparison of two terms of the sort.
      Comparison !Relation !Sort
    | -- | A predicate of the theory.
      PredicateAtom !Name
    | -- | A constructor or a function of the theory.
      Application !Name
    | -- | An integer literal.
      Literal !Integer
    | -- | A variable, with its de Bruijn index.
      Variable !Int
    deriving (Eq, Ord, Show)

-- | Why 'writeSequent' cannot give a term for a sequent.
data WriteError
    = -- | A part of a body or a head that is not a comparison or a predicate.
      NotAnAtom !Formula
    | -- | A term that is not a variable, an integer literal, or an application.
      NotATerm !Formula.Term
    | -- | A disjunct of the head without atoms.
      EmptyDisjunct
    | -- | A variable that no binder of the sequent binds.
      FreeName !Name
    | -- | A function or a predicate that the signature does not have.
      UnknownName !Name
    | -- | The term is not a term of the signature. 'scopedTypeCheck' gives the reason.
      IllTyped !(TypeError SequentSort SequentSymbol)
    deriving (Eq, Show)

{- | The signature of the geometric sequents over the symbols of a theory.
The sorts of the terms are 'IntSort' and the datatypes that have a value. The
signature has the constructors, functions, and predicates of the theory with
these sorts, and the comparisons, literals, and binder sorts of the settings.
Give the signature and 'sequentCodec' to
'Data.CFTA.Gen.ManySorted.Scoped.scopedAutomaton'. That function rejects a
comparison or a binder at a sort that is not in the signature, and a literal,
a comparison, or a binder sort that occurs twice. See Note [Sequents as terms].
-}
sequentSignature :: Theory -> SequentSettings -> ScopedSignature SequentSort SequentSymbol
sequentSignature current settings =
    ScopedSignature
        { scopedBase =
            SortedSignature
                { sortedSorts = map TermSort sorts <> [AtomSort, AtomsSort, DisjunctSort, HeadSort, RootSort]
                , sortedFunctions = structure <> atoms <> terms
                , sortedRoots = [RootSort]
                , sortedValues = []
                }
        , scopedBinders = [Binding (binder sort) [[TermSort sort]] | binder <- [Universal, Existential], sort <- binderSorts]
        , scopedInputs = []
        , scopedBound = sequentBinders settings
        }
  where
    inhabited = inhabitedDatatypes current
    sorts = IntSort : [datatypeSort d | d <- theoryDatatypes current, datatypeSort d `Set.member` inhabited]
    known = all (`elem` sorts)
    binderSorts = sequentBinderSorts settings
    structure =
        [SortedFunction (Universal sort) [RootSort] RootSort | sort <- binderSorts]
            <> [ SortedFunction Implication [AtomsSort, HeadSort] RootSort
               , SortedFunction AtomsEnd [] AtomsSort
               , SortedFunction AtomsCons [AtomSort, AtomsSort] AtomsSort
               , SortedFunction HeadEnd [] HeadSort
               , SortedFunction HeadCons [DisjunctSort, HeadSort] HeadSort
               , SortedFunction Disjunct [AtomSort, AtomsSort] DisjunctSort
               ]
            <> [SortedFunction (Existential sort) [DisjunctSort] DisjunctSort | sort <- binderSorts]
    atoms =
        [ SortedFunction (Comparison relation sort) [TermSort sort, TermSort sort] AtomSort
        | (sort, relations) <- sequentRelations settings
        , relation <- relations
        ]
            <> [ SortedFunction (PredicateAtom name) (map TermSort arguments) AtomSort
               | (name, PredicateDefinition parameters _) <- theoryDefinitions current
               , let arguments = map snd parameters
               , known arguments
               ]
    terms =
        [ SortedFunction (Application name) (map TermSort arguments) (TermSort result)
        | (name, declared) <- theoryDeclarations current
        , let (arguments, result) = case declared of
                FunctionSort parameters value -> (parameters, value)
                value -> ([], value)
        , known (result : arguments)
        ]
            <> [SortedFunction (Literal value) [] (TermSort IntSort) | value <- sequentLiterals settings]

-- | The codec of 'sequentSignature': the variable with the de Bruijn index @i@ is @'Variable' i@.
sequentCodec :: ScopedCodec SequentSort SequentSymbol
sequentCodec = ScopedCodec Variable index Nothing
  where
    index (Variable value) = Just value
    index _ = Nothing

{- | The sequent of a term of 'sequentSignature'. A binder gets the name @x@
and the number of binders around it, so the outermost binder is @x0@. Each
term of the language gives a sequent. A term outside the language gives
'Nothing' or a sequent, because this function does not check the sorts or
the arities: 'scopedTypeCheck' checks them. See Note [Sequents as terms].
-}
readSequent :: Term SequentSymbol -> Maybe Sequent
readSequent = top []
  where
    top scope (Node (Universal sort) [rest]) = do
        inner <- top (boundName scope : scope) rest
        pure inner{sequentBound = (boundName scope, sort) : sequentBound inner}
    top scope (Node Implication [body, heads]) = Sequent [] <$> atoms scope body <*> disjuncts scope heads
    top _ _ = Nothing
    atoms _ (Node AtomsEnd []) = Just []
    atoms scope (Node AtomsCons [item, rest]) = (:) <$> atom scope item <*> atoms scope rest
    atoms _ _ = Nothing
    disjuncts _ (Node HeadEnd []) = Just []
    disjuncts scope (Node HeadCons [item, rest]) = (:) <$> disjunct scope item <*> disjuncts scope rest
    disjuncts _ _ = Nothing
    disjunct scope (Node (Existential sort) [rest]) = do
        (bound, parts) <- disjunct (boundName scope : scope) rest
        pure ((boundName scope, sort) : bound, parts)
    disjunct scope (Node Disjunct [item, rest]) = (\part parts -> ([], part : parts)) <$> atom scope item <*> atoms scope rest
    disjunct _ _ = Nothing
    atom scope (Node (Comparison relation _) [left, right]) = Atom relation <$> term scope left <*> term scope right
    atom scope (Node (PredicateAtom name) arguments) = Predicate name <$> traverse (term scope) arguments
    atom _ _ = Nothing
    term scope (Node (Variable index) []) = case drop index scope of
        name : _ | index >= 0 -> Just (Formula.Var name)
        _ -> Nothing
    term scope (Node (Application name) arguments) = Formula.App name <$> traverse (term scope) arguments
    term _ (Node (Literal value) []) = Just (Formula.Lit value)
    term _ _ = Nothing
    boundName scope = Name (Text.pack ('x' : show (length scope)))

{- | The term of a sequent in the language of a signature from
'sequentSignature'. The names of the binders are not in the term, so
'readSequent' of the term gives the sequent with other names. A variable
refers to the innermost binder of its name. The result is an error for a
sequent that is not in the language. See Note [Sequents as terms].
-}
writeSequent :: ScopedSignature SequentSort SequentSymbol -> Sequent -> Either WriteError (Term SequentSymbol)
writeSequent signature (Sequent bound body heads) = do
    written <- universals [] bound
    _ <- first IllTyped (scopedTypeCheck sequentCodec signature written)
    pure written
  where
    functions = sortedFunctions (scopedBase signature)
    results = Map.fromList [(name, sort) | SortedFunction (Application name) _ (TermSort sort) <- functions]
    predicates = Set.fromList [name | SortedFunction (PredicateAtom name) _ _ <- functions]

    -- The scope holds the bound names with their sorts, innermost first.
    universals scope [] =
        (\writtenBody writtenHead -> Node Implication [writtenBody, writtenHead]) <$> atoms scope body <*> disjuncts scope heads
    universals scope (binding@(_, sort) : rest) = (\inner -> Node (Universal sort) [inner]) <$> universals (binding : scope) rest
    atoms scope parts = foldr (\part rest -> Node AtomsCons [part, rest]) (Node AtomsEnd []) <$> traverse (atom scope) parts
    disjuncts scope parts = foldr (\part rest -> Node HeadCons [part, rest]) (Node HeadEnd []) <$> traverse (disjunct scope) parts
    disjunct scope (binders, parts) = existentials scope binders
      where
        existentials inner [] = case parts of
            [] -> Left EmptyDisjunct
            part : rest -> (\written others -> Node Disjunct [written, others]) <$> atom inner part <*> atoms inner rest
        existentials inner (binding@(_, sort) : rest) = (\written -> Node (Existential sort) [written]) <$> existentials (binding : inner) rest
    atom scope formula = case formula of
        Atom relation left right -> do
            (leftTerm, sort) <- term scope left
            (rightTerm, _) <- term scope right
            pure (Node (Comparison relation sort) [leftTerm, rightTerm])
        Predicate name arguments
            | name `Set.member` predicates -> Node (PredicateAtom name) <$> traverse (fmap fst . term scope) arguments
            | otherwise -> Left (UnknownName name)
        _ -> Left (NotAnAtom formula)
    -- A term, and the sort of its root symbol. The type check compares the sorts.
    term scope current = case current of
        Formula.Var name -> case [(index, sort) | (index, (bound', sort)) <- zip [0 ..] scope, bound' == name] of
            (index, sort) : _ -> Right (Node (Variable index) [], sort)
            [] -> Left (FreeName name)
        Formula.Lit value -> Right (Node (Literal value) [], IntSort)
        Formula.App name arguments -> case Map.lookup name results of
            Just sort -> (\children -> (Node (Application name) children, sort)) <$> traverse (fmap fst . term scope) arguments
            Nothing -> Left (UnknownName name)
        _ -> Left (NotATerm current)
