# Generalized refinements: spike

## Aim

Keep the logical skeleton of `Formula`. Let refinements describe typed values
and named predicates that are defined outside the arithmetic fragment.
Use Kimina to check Lean interpretations. Lower an obligation to Z3 only when
the translation preserves its meaning.

## Representation

Add `Predicate Name [Term]` and `NamedSort Name [Sort]`. Keep applications,
connectives, comparisons, and quantifiers. Keep the existing constructor order.
The names of predicates are global references. Value substitution changes their
arguments. It does not rename a predicate.

The Lean theory gives a named type its arity and Lean interpretation. It gives
a function or predicate its signature and Lean interpretation. A predicate can
instead have a body in the shared formula language. The formula stores names
and terms, not raw Lean source. Explicit Lean interpretations are trusted code.
The theory is fixed for an entailment solver and is part of the language's
meaning.

This spike keeps the `Formula` name and its existing automaton interfaces.
It generalizes the vocabulary. It does not parameterize the entire automaton
implementation over arbitrary syntax types.

## Solver lowering

`lower` validates a query, unfolds shared predicate definitions without
variable capture, and returns the supported Z3 fragment. It rejects remaining
native Lean definitions and named data sorts. The original query must be
well typed, even when expansion would remove an argument.

Replacing a defined function with an uninterpreted function is not an exact
lowering. A countermodel could violate the function's definition. This spike
does not use such a countermodel as `No`.

Solver lowering is distinct from the template lowering of language towers.
It translates logical obligations between backend representations.

## Running example

Use list chunks `[]`, `[1]`, `[2]`, `[1,2]`, and `[2,1]`. Interpret the value of
each chunk as a Lean `List Int`. Compose chunks with append and reverse.
Require the final list to be sorted and a permutation of `[1,2]`.

Use actual LTA guards and the existing measured-constructor path. Check
enumeration, rank/unrank, sampling, and repeated-process rank stability.
Compare accepted programs with an independent Haskell interpretation.
Different programs can compute the same list. Their program ranks remain
distinct.

Use a shared arithmetic predicate, such as `between x lo hi`, to demonstrate
exact definition expansion and Z3 lowering. Check a Lean-only list obligation
that the lowering explicitly refuses. Check that a false list obligation is
rejected through a checked proof.

## Boundaries

The example uses one observed value sort, `List Int`. The current LTA evaluator
copies the distinguished value sort to child values. Mixed observed value
sorts need further design.

This is a partial compiler for the shared language and its definitions.
It does not translate arbitrary Lean source or dependent types to SMT.
An undecided query remains `Unknown`. Exact enumeration must report it.

## Validation

Run builds and tests in `nix-shell` through heavy-management. Use process and
RTS memory caps. Update existing tests. Record measured costs and unresolved
boundaries here before closing the spike.

## Status

Implementation in progress on `spike/refinement-logic`, based on `12273853`.
