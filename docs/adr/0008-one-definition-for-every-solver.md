# 8. One definition gives every solver the meaning of a named function

## Context

A refinement formula can apply named functions and predicates to values of
named sorts, such as `sorted(append(x, y))` over lists. A solver needs their
meaning. Each backend gets it in its own way: Z3 through Liquid Fixpoint knows
arithmetic and unfolds predicate definitions without recursion
(`Data.CFTA.Refinement.Definition`); ground evaluation takes Haskell
functions; an SMT-LIB backend takes SMT text; a Lean backend takes Lean text.
Two spikes decided a finite list language (35 programs over `append` and
`reverse`, guarded by `sorted` and `permutation`) exactly, one with Haskell
functions and one with SMT `define-fun-rec`. Nothing checks that the Haskell
code, the SMT text, and the Lean text agree. A `define-fun-rec` that does not
terminate makes Z3 give wrong answers. A Haskell function cannot be stored
with a language, so a saved language reloads only with the same code.

## Decision

A theory declares datatypes and defines functions and predicates in the
formula language:

- A datatype has a name, sort parameters, and constructors with typed
  fields. A constructor application is an `App` of the constructor name.
- A definition has typed parameters, a result sort (or a formula, for a
  predicate), and a body. A body is a term or a formula, or a case split on
  one parameter or bound field: one branch for each constructor, which binds
  the fields of that constructor.
- A definition calls itself only with a field that a case split of the same
  parameter binds, in the place of that parameter (structural recursion). It
  calls other definitions only when they come earlier in the theory.

Every backend reads the same theory. Ground evaluation interprets the
definitions. The SMT-LIB backend declares the datatypes and the definitions
(`declare-datatypes`, `define-funs-rec`). Unfolding continues to serve Z3
through Liquid Fixpoint for definitions without recursion. A Lean backend
translates the same definitions. A Haskell interpretation stays possible for
a name that has no definition. The text format stores the theory beside the
predicate definitions (`definitions 1;`, not released yet).

## Why

- Two backends can disagree only when one of them is wrong, not because two
  texts of one function differ.
- Structural recursion terminates: each recursive call takes a strict
  subterm. A syntactic check is enough, Z3 and Lean accept the definitions,
  and ground evaluation stops.
- Declared constructors are free, and a datatype with a constructor without
  recursive fields has a value. These are two of the conditions under which
  ground evaluation can give `No`. The declarations now state them.
- A theory is data, so a language and its theory save and reload without
  code.

## Consequences

- `Formula` and `Term` do not change. A case split exists only in definition
  bodies, so no traversal of formulas gets a new case.
- Mutual recursion, recursion on two parameters at once (such as `merge`), and
  recursion on integers are out of scope. Such a function stays a Haskell
  interpretation or a native definition of one backend.
- Liquid Fixpoint prints `define-fun` and has no `define-fun-rec`, so
  recursive definitions reach Z3 only through the SMT-LIB backend.
- An inductive fact, such as `reverse(reverse(xs)) == xs` for every list,
  stays `Unknown` for ground evaluation and for Z3. Only a prover with
  induction decides it.

## Discussion points

- Trusted text for each backend, as in the spikes: rejected. Nothing ties the
  texts together, and SMT recursion can fail to terminate.
- A `match` term in `Term`: rejected for now. Every traversal of terms
  (lattice, Z3 translation, generators, text format) would change, and case
  splits in definition bodies cover the same functions.
- Testers and selectors, as in SMT-LIB, instead of case splits: the check of
  structural recursion would have to follow the tester guards.
- Termination by a measure, as in Liquid Haskell: more general, but it needs
  a solver to check. Possible later.
- Prior art: SMT-LIB 2.6 datatypes and `define-funs-rec`; Liquid Haskell's
  refinement reflection and proof by logical evaluation (Vazou et al.,
  "Refinement Reflection: Complete Verification with SMT", POPL 2018); Lean's
  structural recursion.
