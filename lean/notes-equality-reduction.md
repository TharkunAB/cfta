# Equality path filtering and repeated reduction

The source is `Data.CFTA.Equality.Operations.reduceEqConstraints`,
`requireAll`, and `editAll`. Node path projection and intersection come from
`Data.CFTA.Interned.Operations`.

`PathFilter` implements the constructor-copy action for ordered path-edit
plans. Each copied transition retains its symbol, child order and original
guard. A terminal edit adds its predicate at the selected subtree. The source
requires missing paths in `requireAll`; `editAll` ignores missing paths.
`at_exact` proves both cases. `restrict_exact` proves soundness and completeness
of the copied graph. The representation expands sparse child keys to ordered
prefixes. Its sparse trie adapter remains separate.

`EqualityNarrowing` uses the actual graph projection from `SymbolicGraph`.
That projection can overapproximate the set of subterms, but it contains each
subterm of every accepted original term. `selected_common` derives the shared
subtree in the other-path intersections of a nontrivial satisfied class.
`edit_preserves` proves that the selected-path edit retains this term even
after earlier edits have narrowed the current graph. `edit_sound` proves that
the edit cannot add an original rejected term. `require_preserves` proves that
requiring each class path cannot remove a satisfying term.

`EqualityReduction` ports the source reduction schedule over node identities
and ordered child lists. It selects classes against the original child list,
requires their combined paths, reduces classes in right-fold order, and
propagates structural empty children. Each class computes all its projected
intersections before it applies its edits. The model retains the source's
first-element seed and right-fold order in `intersectList`.

`pass_exact` derives preservation for one complete pass.
`constrained_pass_exact` retains both original constraint sets. This is the
current public `reduceEqConstraints` behavior after PR #89. `reduce` repeats the
pass until child identities stop changing. `constrained_reduce_exact` proves
that every completed repeated reduction preserves exactly the forest terms
satisfying the original local and inherited constraints. It derives the
absence of root paths from finite-term satisfiability. It does not assume
that the reduction loop preserves languages.

The `Laws` structure lists eight local graph requirements: empty meaning,
intersection meaning, projection coverage, narrowing and preservation for
required paths, narrowing and preservation for batched edits, and sound
contradiction detection. Explicit graph intersection, projection, path-copy
and equality-normalization proofs supply these semantic components. The
remaining adapter must connect the actual sparse `Needed`/`Edits` tries,
interned forest operations, and recursive blocking decisions to those laws.
The complete `reducePartially` inherited-constraint caller also remains to
be connected. Fuel exhaustion is not an empty language. General fixed-point
termination is not proved.

Validation: the pinned Lean build checks all three modules without proof
placeholders or additional axioms. An independent Nix source check covers
5,000 finite overlapping/equality grammars. It compares reduction, repeated
reduction, trim and redundant-edge removal against explicit expected term
sets, counts, rank inverses and invalid-rank rejection. Those source checks
support the correspondence review; they do not prove the remaining adapters.
