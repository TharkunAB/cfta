# 4. The explicit graph is the semantic boundary of the exact paths

## Context

Constructions build interned nodes. `createMu` finds the shape of a binder by
calling its body with placeholders, a union inside an open binder stays
deferred (`InternedUnion`), and the memo tables key on the identities of
records that construction may not have finished. That is fast, and
intersection, equality reduction, and merging depend on it. But an exact
query (list, count, or rank the accepted terms of a size) then reads the
recursion back out of those records, and a proof of such a query must reason
about the probes. The Lean formalization has about 226 modules for the
interned constructors alone, and its reference semantics is already a finite
graph of states and transitions.

## Decision

Exact listing, counting, and ranking of accepted terms are defined and
computed on the explicit graph, `Data.CFTA.FTA`: states, transitions, and
explicit references to states. An interned automaton enters through `toFTA`,
once, after construction. The interned core stays for construction, and for
intersection, equality reduction, and merging.

## Why

- The proof splits into two smaller parts: the exact queries on a finite
  graph, which the Lean model already has, and `toFTA`, which reads only
  finished nodes. The probes stay a question of construction.
- The interned core is already optimized, so it stays.
- `Data.CFTA.Sized` shows that the route works. On an `FTA` it gives exact
  size classes for cyclic, ambiguous, and equality-constrained automata, and
  it uses the count table of the cyclic import where that applies.

## Consequences

- `toFTA` is the one adapter between the two forms. It replaces the `rowsOf`
  snapshot that the Lean model assumes today.
- A new exact query goes on the graph. An operation on interned nodes enters
  an exact path only as an exact transformation before `toFTA` (`CONTEXT.md`,
  "Transformations").
- The ranks of a size class follow the structure of the graph (row order), so
  a transformation that changes the structure, such as reduction or pruning,
  can change the ranks, but not the classes.
- The UVar enumerator stays on interned nodes as the fast route for
  constrained listing. It does not define the language.
- The cyclic import still reads its rows from interned nodes (`rowsOf`). It
  can read the rows of `toFTA` instead, so that one adapter feeds every exact
  query.

## Discussion points

- One graph core for every operation, from a design study of 2026-10-10:
  rejected. It changes where enumeration truncates recursion, moves
  structure-based checksums, needs a canonicalizer for
  `withoutRedundantEdges`, and puts the 5% budget of the acyclic hot path at
  risk. On small recursive automata its intersection was about 9 times
  faster, and an import of a dense strongly connected component grew
  factorially. Matti on the interned core: "already highly optimized, so we
  don't want to replace that".
- Proofs of the constructors and their probes continue in the formalization,
  but no exact query depends on them.
- The wishlist of the formalization asked for the explicit graph as the
  semantic core. This decision takes it as the core of the exact queries only.
