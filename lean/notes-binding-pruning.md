# Binding and pruning control flow

`Binding.lean` describes finite recursive shapes before interning. An edge
payload contains its symbol and constraint. The model retains live binder
identities and masks each local reference during substitution.
`substitute_congr` proves that substitution reads only free references.
`restrict_correct` and `binding_cache_key_sound` justify the source cache key
that stores only those environment entries. `closed_unchanged` justifies the
closed-node shortcut. `identity_substitution` proves replacement by the same
reference. Both shape probes participate in `BinderKey`; equal ordinary
shapes cannot hide different depth probes.

The source `createMu` function requires a body that is parametric in its
reference argument. The model does not establish that property for arbitrary
Haskell callbacks. The source's fresh binder allocation and alpha-renaming
must refine the retained-identity model. Capture-free replacement needs that
connection. The structural cache theorems do not establish language
preservation for arbitrary captured references. Concrete interning and
memoization use the separate `Cache` invariants.

`PruneSchedule.lean` ports the candidate decision loop in `pruneSemantic`.
A fully decided pass returns exactly the successful specialized edges, in
source order and with their multiplicity. An ambiguous unknown result returns
the original whole edge, including its guard. It discards the accumulated
specializations. An unambiguous unknown result returns `PruneUnknown` even
when earlier candidates succeeded. A read through an unfinished recursive
binder also retains the whole edge.

The driver ports `pruneNode`, `pruneMu`, the ordered child traversal, empty
child rejection, and cache insertion after completion. It registers a binder
before pruning its body. It rebuilds that binder and repeats when its identity
changes. The model passes state changes from specialization to later edges.
Fuel exhaustion is a separate result. It is not successful emptiness and it
does not assert that the Haskell fixed point terminates.

`ObservationGraph` supplies the checked finite specialization algorithm.
`PruneSchedule.Operations` identifies the remaining source interfaces:
interned graph views, equality narrowing, semantic queries, specialized-node
memoization, and binder rebuilding. This operational port does not prove
those interfaces exact by assumption. Its proved results are the decision
loop, reference preservation, and cache-hit behavior. Full driver language
preservation requires representation invariants and the correspondence of
those operations. The recursive termination obligation remains open.
