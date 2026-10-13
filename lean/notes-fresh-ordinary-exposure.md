# Repaired ordinary probes and prepared cold exposure

The local source repair changes the ordinary placeholder in Mu construction.
`InternedStoredSubstitution.execute` uses the earlier construction executor.
The new adapter states exactly where that earlier executor still describes
current source reconstruction.

`InternedFreshOrdinaryStoredSubstitution.build_eq`, `buildMany_eq`, and
`buildEdges_eq` prove exact result equality for binder-free syntax. The result
includes the complete returned cache. These theorems need no cache invariant.
The encoded plan for a `PreparedWithoutMu` value is binder-free. `execute_eq`
therefore proves exact stored-executor equality from preparation alone.
`unfold_eq` derives the needed body preparation from an available record in a
`Prepared` cache. It uses the repaired executor in the new `unfold` definition.

`MergedFreshOrdinaryExposure.collect` and `nodeEdges` retain the original
worklist order, direct Mu fast path, visited identities, and closure fallback.
They call the repaired stored executor. `collect_eq` and `nodeEdges_eq` prove
exact equality with the earlier exposure result at every fuel bound, under
`Facts`, `Prepared`, and availability of the actual inputs. The proof derives
these premises at each intermediate returned cache. It preserves unresolved
references, pending results, and fuel exhaustion as separate outcomes.
`read_eq` lifts this equality to the comparison reader. Thus each actual cold
merge read covered by those invariants has the same result after the repair.
The comparison control flow, selection, and ordinary merge constructors do
not change in this adapter.

`nodeEdges_verified` transfers the existing cold reader invariant to the
repaired reader. `read_closed` transfers successful closed exposure and its
stable fuel bound, returned edges, preparation, and exact cache histories.
No warmup or ready-cache premise is added.

This bridge does not prove equality outside `PreparedWithoutMu` reconstruction.
Open nested Mu plans can issue binder requests and can distinguish the two
executors. The preserved old pending counterexample is therefore not erased.
This bridge also does not assert global termination for repaired construction.

Validation: Lean 4.34.1 builds both new modules. The isolated dependency audit
permits only `propext`, `Classical.choice`, and `Quot.sound`.
