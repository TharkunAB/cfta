# Canonical cached selector source review

Status: SOURCE CLEAR. Reviewed on 2026-10-24 at 01:35 CEST. No compiler or candidate program was run. This review identifies no static type or mathematical blocker in the complete 190-line selector and 239-line canonical waiting module.

Root authored the selector. Guard authored canonical waiting. Arity authored the compression-frame foundation; Root repaired its proof substitutions and added field documentation. This review is independent of the two reviewed modules. It is not an independent reproof of the frame foundation.

The reviewed identities are:

- `/tmp/mcfta-cached-selection-20261024-selector.lean`: `c5c57b1a8c3afe7f3dfe8ad8d7ad79d6deaaac833d0fc82bf4ff12c50ecb82b5`.
- `/tmp/mcfta-cached-selection-20261024-canonical-waiting.lean`: `fcb7c910fb67bf253bfb7c6b5ed9d1bb1f5e186cb78cf18f52e7a9cbe7dbdd70`.
- Compression-frame dependency: `5b6e6a4b11c21b949874db500e23aa074fcdd4e0de683f46f33863113dc91375`.
- Repository HEAD: `65f237954c3e867570c06d2de22681f55ca64fcd`.

`canonicalValue` changes only suspended variable IDs. It retains node IDs, tries, occurrence order, and multiplicity. Enumerated and eliminated values remain exact. `Correct` uses this ghost count view. It does not replace stored runtime values.

Canonical replacement removes all old occurrences before it adds the new occurrences. Its proof reduces to the existing raw count theorem through `List.map_set`. The support theorem derives each waiting key from an actual stored suspended reference. It does not assume the selector's result.

`move_correct` covers equal source and target keys, an absent source bucket, and a positive source bucket. The target receives the source count plus its previous count. The old key is deleted. `moveMany_correct` composes the matching bucket operations and ghost redirects in the same order. No root-fixed premise is necessary for this count equation. No native union or forest theorem is asserted.

Selector `Correct` deliberately separates the index equations from actual forest paths. `frame_correct` retains a fixed root map and the exact slots and supply. It does not claim that an arbitrary replacement forest has that root map. `transfer_correct` changes the ghost map and waiting counts; it does not produce `Roots` for the unchanged forest.

`candidates_exact` preserves increasing slot order and matches the complete pending list used by the stop test. `find_exact` derives canonical blocked support from the count invariant and `scan_blocked`. Filtering preserves candidate order. An empty candidate list gives `none`; a nonempty list with every candidate blocked gives `some []`.

`next` uses the existing `pickNext` rule. It therefore retains the existing valid-preference and fallback behavior. The module adds no stop or narrowing execution. The candidate theorem identifies the full list before blocked subtraction, as required by the existing stop test.

`findAction_represents` is an equality of rank-polymorphic CPS computations. It gives one exact result with the same complete modeled `Cached` state. This includes both cached indexes, all five nonforest core fields, and the literal forest. It is stronger than equality of only the returned candidate list.

`scan_agrees` requires both the index equations and actual `Roots` paths. It derives totality from those paths, then combines the existing exact scan result with the full compression frame. Its conclusion allows the old scan to compress the forest while preserving every root ID and size. It does not equate the old scan's final forest with the pure action's input forest.

`scan_complete` obtains a real finite successful old scan from `findExpandable_terminates`. It then identifies the result by `scan_agrees`. The bound is existential. No same-fuel success is promised between different related forests.

The source correspondence matches `cfta/src/Data/CFTA/Enumeration.hs`: canonical counting at lines 458–464, bucket transfer at lines 737–743, and pure candidate-minus-waiting selection at lines 827–837. The current source uses gained/lost deltas, while the model's replacement theorem uses complete old/new slot values. Connecting each actual delta and completed union/assimilation transaction to these equations remains a separate proof obligation.

The modules do not establish canonical index reachability for every native mutation, native union realization of the ghost redirect, preservation between intermediate transaction writes, or full driver observation congruence under compression. The old raw-key cached invariant is not used as a substitute for canonical correctness. These boundaries are consistent with the stated result.
