# Actual native union and Mu branch witnesses

Updated: 2026-10-14 19:37 CEST.
Proofs: `9b6d9014` and `513d2824`.

## Actual union normalization

`SourceRecursiveIntersectionKernel.union_readback` derives the exact ordered
walk, intermediate valid machine, available returned values, actual union
constructor work, and cache growth. The result retains every source member
occurrence before normalization.

`union_values_replay` replays each original member result in the same later
cache. It retains ordered operands and duplicate occurrences. Actual union
constructor work also returns the same value without allocation there.

`union_language` proves that the actual normalized value has exactly the
union of the independent guarded languages of these returned values.
`union_language_calls` states the same equation through actual successful
member calls. It does not choose a public closed child map. Coherent actual
constructor facts and callback replay supply these results. No two-input
product-language contract is assumed.

## Actual Mu construction

`mu_body_replay` derives the original operand identities, exact extended
domain key, retained canonical domain, and actual body representative.
The key retains original free bindings and the source's sorted recursive
pair. The exact domain allocation replays without changes in every later
cache. Both the body request and the actual optional binder retain their
exact results there. Physical and domain histories remain separate.

`mu_language` proves the independent least language of this actual body at
the original repeated-pair reference. It uses the existing actual optional
binder proof and the semantic and independent-language probe heaps in the
later cache. These heap premises are explicit at the generic kernel entry.

`mu_language_calls` states the least equation through successful body calls
in that exact extended domain. `mu_unfold_language` proves the complete
unfolding equation when the repeated-pair reference receives the returned
value's own language. Monotonicity is derived from independent stored meaning.
The least-language theorem remains explicit. An arbitrary fixed point is
not sufficient to establish the intended result.

## Checked native execution

`SourceRecursiveIntersectionNative.native_node_branch_replay` starts with an
actual completed native call and checked `WordRanges`. It derives the exact
allocation-free source branch at every larger recursive kernel bound and
every later cache. No kernel-execution premise is supplied.

`native_left_union_language` and `native_right_union_language` derive ordered
actual child results and exact independent union language for both operand
orientations. `native_mu_language` covers both-Mu, left-Mu, and right-Mu
branches. It retains the original operand identities, extended key, canonical
domain, actual body call, and complete independent least language.

The native Mu entry requires the semantic and independent-language probe
heaps of the incoming machine. Actual native evaluation derives their
preservation. It does not assume those heaps at each reached binder.
Source availability, selected branch, native validity, checked word scope,
and exact returned value remain explicit.

## Remaining product obligation

These results prove how actual branch outputs relate to their actual child
outputs. They do not prove that each output represents its original input
intersection. That complete two-input law remains open.

Next derive a consistent relation from original input pairs to physical
representatives through stored reconstruction and repaired unfolding. Use
the exact extended-domain and body witnesses above. Preserve related children
through the actual optional-binder substitution. Follow epsilon origins for
Mu and union before comparing complete exposed rows. Do not use the literal
ordinary `nodeEdges` projection as the exposed Mu or union row table.

Then derive related roots and local row closure. Apply the completed
`RelatedRows`, `DiagonalProduct`, native minimum callback, and compiler Sized
results. Do not assume product language as a premise. The general functional
child map remains refuted by the retained ranked Mu witness. Preserve that
witness, the exact unbounded transcript proof, and all older functional
proofs for their stated scope. The optimized interned core stays unchanged.

## Validation and preservation

Pinned Lean 4.34.1 passes all three focused modules and the aggregate audit:
1,473 jobs and 43,911 theorem dependency checks. Only `propext`,
`Classical.choice`, and `Quot.sound` are permitted. All new completed modules
are imported by `MicroCFTA/Audit.lean`.

Audit: `/tmp/mcfta-union-mu-branch-readback-20261014-audit.log`.
Focused logs: `/tmp/mcfta-union-readback-build.log`,
`/tmp/mcfta-mu-readback-build.log`,
`/tmp/mcfta-union-mu-call-languages-build.log`, and
`/tmp/mcfta-native-branch-readback-build.log`.

Snapshot: `/tmp/mcfta-union-mu-branch-readback-checkpoint-20261014-1937/`.
All 1,840 Lean-tree files are saved. All 1,836 previous files remain. Only
audit imports, two coverage ledgers, and the preceding relational-product
note changed among them. Earlier proof and marked-draft bytes remain.
Both untracked fixtures, all backups, stashes, and worktrees remain.
No production Haskell code or committed test changed. Prior Nix and formatter
evidence remains applicable. No background proof worker remains. All work
stays local. Weekly allowance is 27 percent; stop at 1 percent or less.
