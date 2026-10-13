# Shared row adapter and cyclic queries

Source: `origin/microcfta` at `7989e91a` (PR #115).
The local continuation was rebased on that source. The rebase preserved all
1,432 saved Lean-tree files, including drafts and the untracked fixture.
Backup: `backup/formalization-before-rebase-20261013-2315` at `298a225b`.
The rebase completed at `5d5ac947` before new work.

## Actual row extraction

`SourceInternedRows` follows `reachable`: skip EmptyNode, skip visited IDs,
store the exposed row, and prepend children in their source order.
`SourceInternedRowsFinite` proves exact visited keys, finite completion on a
closed finite exposure snapshot, and equality with functional map insertion.
`toRows` reads those keys in ascending order. Its transitions retain the
symbol, complete constraint, and ordered child list. EmptyState is separate
from every nonempty identity.

`SourceInternedRowsLanguage` proves the exact guarded language and ordered
readback at every declared state. It makes no assumption that `toRows`
already preserves language. `SourceInternedRowsValidated` proves open-root
rejection before traversal, successful normalized `toFTA` readback, and
finite validation including possible arity errors.

A nonempty table omits EmptyState. Validation therefore needs the retained
edge invariant that no child is EmptyNode. `SourceInternedRowsHeap` derives
this fact from the issued-row representation. It also derives a finite closed
identity domain from cache validity and child availability, and connects
actual intern operations to exact exposed rows.

The front-end snapshot still needs native heap identity, recursive
`nodeEdges`, and `freeVars` readback. The traversal proof does not establish
those construction facts by itself.

## Finite keys and canonical order

`SourceDenseRows` follows `zip (Map.keys rows) [0..]`. It derives map lookup,
the exact dense range, and both key/index roundtrips. The finite state carrier
contains only declared keys; it does not contain every possible interned ID.

`SourceDenseRowsCanonical` computes canonical classes on that dense carrier
and sorts the original transitions. It proves exact class transport, stable
transition order, size-class enumeration, counts, and signed selection.
Custom symbol keys can collide. These proofs retain symbols and constraints;
they do not identify terms with equal custom keys.

`SourceDenseRowsRestrict` constructs each child membership proof from closed
raw rows. Forgetting the finite carrier recovers the complete original row
sequence. Guarded acceptance and first-occurrence size classes are unchanged.
Completed `toRows` supplies the root membership and all readback facts.

## Minimum sizes and cyclic query composition

`SourceRowsMinimum` proves convergence of the actual right-fold minimum-size
recurrence using only the finite row-map keys. The state type can be infinite.
The result is the exact least structural node count, or absence when no finite
term exists. `SourceRowsMinimumShape` proves child-shape invariance for every
sweep and the final result. Arbitrary constraint replacement, unit erasure,
and noninjective symbol relabeling leave that calculation unchanged.

`SourceRowsMinimumAdapter` uses actual shared adapter rows and distinguishes
EmptyState from every identity. `SourceRowsMinimumPublic` connects the
`nodeEdges` empty check and minimum-table membership to the original exposed
heap's finite structural language. It derives a finite traversal and minimum
calculation. Constraints are not evaluated by structural productivity.

`SourceRowsMinimumGate` derives the real overlap callback from those minima
under the intersection product-row contract. It does not assume a separate
productivity oracle. Native intersection construction and its row contract
remain explicit boundaries.

`SourceCyclicRows` constructs the sorted input to the existing cyclic query
proofs. It derives the old arbitrary sorted-row/permutation premise from
dense canonical preparation. Its prechecks retain the empty/open/constrained/
ambiguous order. `SourceCyclicRowsReadback` constructs that input from actual
completed `toRows`, then proves exact original guarded language, finite
class counts/decoders, and both inverse laws with rejection.

`SourceCyclicRowsExecution` adds the convergent minimum-size prepass before
the finite count/plan query. The class certificate bounds recursion nesting
by node count plus one. It is not a primitive machine-cost or lazy heap bound.
`SourceCyclicRowsNativeGate*` now connects the actual native minimum-row
callback and complete ambiguity scan to the reference synchronous test.
It derives plain source readback from the real constraint precheck. A scoped
product-row construction contract remains; no separate productivity oracle
or global erased-heap contract is assumed. The compiler result, finite
completion, exact size classes, and inverses transfer through this equality.

`SourceInternedIntersectionRows*` executes the ordinary construction kernel
through physical caches: source hash join, arity check, child sequencing,
edge creation, surviving rows, and canonical node readback. It derives
correct common language for finite plain operands in the actual physical
cache. `sizeOf left` gives sufficient fuel. Larger fuel retains both the
output and final cache. Native memo/self/order dispatch and recursive
Mu/union exposure remain separate. This kernel theorem does not discharge
the general scoped product-row contract.

## Concrete cyclic probability records

`SourceCyclicRowsProbability*` constructs the current cyclic sampling record
from compiled counts and selectors. It derives the Exact backend's uniform
selection, singleton shortcut, public PMF, empty/nonpositive-size behavior,
normalization, reciprocal term mass, complete positive support, and sampled
rank replay. Shared-row readback identifies these outcomes with the original
exposed guarded heap. No sampler normalization premise is assumed.
An arbitrary PRNG still needs its stated uniform-draw law.

## Custom-key tie counterexample and source correction

The source comment claimed that canonical child classes made cyclic rank
order independent of interning order. This needs a qualification when distinct
symbols have the same supplied key. Equal arity, supplied key, and child-class
list leave a stable-sort tie, so the source row order remains observable.

`repro/CyclicKeyTies.hs` uses a cyclic grammar and the constant key `()`.
Run separate processes with `tie-a` and `tie-b` to choose the first interned
constant. Size-one output changes from `[tie-a,tie-b]` to `[tie-b,tie-a]`.
`SourceCyclicRowsKeyTies` checks the same sorting boundary and different
rank-zero terms with unchanged counts. The source comments now state that
complete key ties retain source order. Runtime ranking behavior is unchanged.
This finding does not refute the count or inverse laws.

## Validation and scope

The shared-row checkpoint passed 1,123 targets and 38,793 theorem dependencies.
The later native-gate, probability, ordinary-intersection, and solver-name
batch passes 1,140 targets and 39,108 theorem dependencies. The audit permits
only `propext`, `Classical.choice`, and `Quot.sound`.
Logs: `/tmp/mcfta-one-row-20261013-audit.log` and
`/tmp/mcfta-native-liquid-20261013-audit.log`.

The rebased source passed 285 core, 206 generator, and 144 refinement examples
in Nix. Log: `/tmp/mcfta-one-row-20261013-tests.log`.
The tie reproduction passed in separate native processes.
Log: `/tmp/mcfta-key-ties-20261013.log`.
Fourmolu and cabal-gild checks passed in Nix.
Log: `/tmp/mcfta-one-row-20261013-format.log`.
No production test or benchmark formalization was added.

The existing Sized, liquid, probability, and bounded import proofs remain.
Native immutable exposure, intersection construction, complete custom-order
fallback compilation, concrete storage, and lazy runtime execution still
need their stated adapters. Older constructor and equality drafts remain
secondary targets. Do not infer whole-library completion from this audit.
