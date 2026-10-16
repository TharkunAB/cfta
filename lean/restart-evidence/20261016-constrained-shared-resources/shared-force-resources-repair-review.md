# Shared Force resource elaboration repair

Validated 2026-10-16 21:01 CEST.

Final source SHA: `24e22be723b82f2015702fa760bdb8404ee2f6e713ec29532624362bebe1e8c2`. The source has 157 lines.

The failed canonical draft used ambiguous `State` after opening both `Cache` and `SharedTargetState`. The repair imports only `store` from the shared namespace and uses a local `Shared` notation for every shared-state type. The final two supply proofs also unfold `store` explicitly so the returned checked-heap projection reduces before the arithmetic comparison. No public premise, conclusion, resource definition, actual graph, or semantic proof flow changed.

Direct check 2 passed with exit 0 and no warnings. The initial direct repair check is retained. It found only the two final reducible store projections. The original failed canonical log and exact pre-repair source are retained. `shared-force-resources-repair.patch` records every edit. No canonical build was run by the repair owner.

The receipt assembly uses the same Target actual, reads, checked return, and saved Merge memo. A miss stores that exact result and uses public `Ready.store`. Selected-language inclusion comes from the actual Target receipt and coherent nontrivial class facts. A hit uses the existing semantic SlotReceipt for availability and inclusion, the separate slot profile certificate for shape and height, and an empty Work trace at the identical whole shared state. It performs no query or allocation.

The new slot profile is proved from the actual constructed Target and the exact other-path count. Native, output, and Merge certificate fields come from that same Target construction. Initial slot-sensitive headroom derives every query entry through the constructed Target resource theorem. Final request counts and supply bounds use its same actual Work trace. The helper receives no future range plan, output profile, completion callback, or final invariant.

The bounds apply to constructor Work and its two supplies. Equality operation allocation, native table allocation, host resources, and runtime demand correspondence remain separate. No Haskell repair was made or identified. No process remains active.
