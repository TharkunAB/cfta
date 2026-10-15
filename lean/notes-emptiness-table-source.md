# Explored emptiness tables and actual source row reads

The reached delayed trace and entry-derived inventory are now checked at
`2a1e918e`. Read [the current next target](notes-delayed-emptiness.md).
The source Task/Force/Expose composition and final native entry validity
remain open. The checkpoint and next-target statements below are historical.

Source main: `a22b2ad46ffcad57a77b64447c18da7b0850f52f`.
Starting checkpoint: `7b270679`. Proof commits: `76afeec1`, `e736beeb`,
and `71b7fd08`. Read [the source update](notes-main-a22b2ad4.md) for the
Haskell comparison and retained raw-class boundary probes.

## Finite table execution

`ConservativeEmptinessTable.Key table` contains exactly the keys in the actual
completed table. The table supplies a complete finite list of that subtype.
The proof does not require every mathematical integer to belong to a finite
list. Row order and requirement order are unchanged. Empty requirements are
false. Missing keys remain possible requirements and remain absent from every
known set. The closed bit does not affect fixed-point reads, as in the source.

The literal raw OR-of-AND operator agrees with the finite-carrier operator.
Each synchronous round has exact readback. Rounds ascend, stabilize, and give
the least closed set. The equality-stop worker returns its current set when
the next set is equal. Every completed run from an actual synchronous round
returns the same least fixed point. Starting from false, table.length + 1
equality checks suffice. Equality is checked only at stored keys; all absent
keys are false at these actual rounds, so this gives complete set equality.

`ConservativeEmptinessTableSoundness` proves that empty-start exploration stores
exactly the supplied rows at every admitted key. It derives ordered row
agreement and the existing smaller-witness decomposition. The actual admission
bound gives budget + 1 equality checks after row computation. Its emptiness
theorem uses certified physical readback, three primitive semantic laws, and
one-level accepted-row exposure. It assumes neither Decomposes nor correctness
of the complete analysis. Native IntMap/IntSet storage and row production
remain separate source transfers.

## Untagged physical keys

`SourceEmptinessKeys` reads the untagged original node identity. An interned
reference can share its binder's identity. A closed nonempty value instead
has an allocated constructor entry. Common-heap coherence and availability
then make equal untagged keys identify equal complete records across all
allocated constructor kinds. The proof does not use tagged-key equality as
a substitute for this statement.

`Closed heap` contains actual available values whose cached free list is
empty. Finite inventory search computes physical readback. Every stored table
key must occur in that inventory. Coverage and coherent residency identify
the literal stored node. Missing keys classify as outside. Empty identifies
the actual EmptyNode. This derives the row theorem's Readback on the certified
domain. The same unrestricted theorem is false on arbitrary raw Value records.
Closedness and residency are required proof-domain conditions.

`SourceEmptinessTableSoundness.excludes` composes this derived physical
readback with the literal finite-table theorem. Its conclusion excludes terms
in the original guarded meaning. `explored_excludes` also derives stored-row
receipts from empty-start exploration. The caller still supplies inventory
coverage, certified primitive operations, and accepted-row exposure.

The key helper embeds natural identities with Int.ofNat. It does not establish
the source machine-Int encoding, allocation capacity, or absence of reused
identities. Those representation obligations remain explicit.

## Actual exposure and class operands

`SourceEmptinessExposure` uses actual completed nodeEdges reads and their full
returned constructor caches. The read retains normalized stored equality
fields. Acceptance of a complete edge constraint implies satisfaction of the
actual equalities accessor. This includes positive guard extraction and
residual guards. An accepted row cannot have EqContradiction. The source
filter therefore retains a row with its original children, satisfied classes,
and derived nontrivial normalized classes. Stored class order remains intact;
this is not subsumption order.

Its `source` theorem derives finite construction and finite row reads from
the original closed lexical expression. Normalized original annotations
supply the field invariant. Independent source-syntax acceptance supplies
the accepted retained row. No successful-construction premise or accepted-row
oracle is supplied.

`SourceEmptinessProjection` retains actual getPath calls without
mergeAlternatives. Projection returns a closed available result. The wrapper
retains native node and edge memo tables and the intersection domain state.
Finite projection completion and proper-subterm inclusion are derived from
the existing physical projection proofs.

`SourceEmptinessClassFold` retains the two different source schedules. For
paths [a,b,c], the analysis projects a,b,c, intersects b with c, then intersects
a with that result. The seeded refused-class helper projects b,c,a, intersects
c with a, then intersects b with that result. Seed rotation expresses the
second schedule without identifying its native states with the first.
Its empty-list fallback returns EmptyNode without effects. Literal foldr1
has no empty-list result. Normalized nontrivial classes exclude that case.

For closed operands, nodeMemoKey exists even for EmptyNode. The source reads
both operand keys before the native body checks emptiness. An unresolved raw
placeholder can bypass the second key. The fold theorems require closed
available operands and do not claim that demand schedule for raw placeholders.

Completed folds derive closed result availability and physical history. Every
common accepted selected subtree survives. A satisfied nontrivial class gives
an accepted subtree with strictly smaller term height. The proofs retain the
actual native Step leaves and returned full states. They do not derive general
fold completion or the leaves' word-range checks.

These folds use the existing scoped native engine. They do not yet transfer
to the newer checked constraint-operation allocation state. They also do not
prove GHC demand, first-installed thunk ownership, or native container adequacy.

## Next source connection

Model the stateful worklist of delayed requirements. Original child values
precede the class-intersection thunks in each stored row. Source exploration
forces each queued item before checking budget exhaustion. A class thunk
must retain its captured original forest and actual fold result at its reached
cache state. Do not evaluate all class intersections before child traversal.

Derive stored-key inventory coverage and closed available requirements in one
final coherent heap. Connect source exposure and both fold receipts to the
certified primitive operations and table supply. Then instantiate the proved
table soundness for each actual oracle call. Carry both gate modes and all
three gate memos through the lazy refused-class scan and selected fallback.
Whole current reduction and repeated-pass termination remain unproved.

The broader native input checks, semantic finish receipts, internal ranges,
sidecar allocation coverage, and candidate-parametric Mu/repeated-pair law
remain. Keep the optimized interned core, older constructor/equality targets,
all counterexamples, and all marked drafts. Full-library correspondence,
derived-refinement frontends, named measures, codecs/parser bridges,
getAllAtPath, decision-model, runtime representation, and extraction remain
open. Sized exact classes, finite execution, canonical sequence, distinct size
order, and both signed inverse directions remain separate contracts.

## Validation

The full pinned Lean build passes 2,006 jobs. The audit checks 51,337 theorem
dependencies. Only propext, Classical.choice, and Quot.sound occur. No new
warning occurs; the old unused-input warning remains. Logs:

- `/tmp/mcfta-emptiness-table-audit-20261015.log`
- `/tmp/mcfta-emptiness-source-focused-20261015.log`
- `/tmp/mcfta-emptiness-physical-soundness-20261015.log`
- `/tmp/mcfta-emptiness-class-fold-20261015.log`
- `/tmp/mcfta-conservative-emptiness-table-axioms-20261015.log`
- `/tmp/mcfta-conservative-emptiness-table-soundness-axioms-20261015.log`
- `/tmp/mcfta-source-emptiness-keys-axioms-20261015.lean`

All four Haskell package trees are unchanged from 7b270679. The previous strict
Nix build, 697 examples plus golden suite, changed-file Fourmolu, metadata,
and separate Sized rank checks were not repeated for this proof-only change.
