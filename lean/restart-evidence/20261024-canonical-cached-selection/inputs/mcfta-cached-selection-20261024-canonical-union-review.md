# Canonical union source review

Reviewed at 2026-10-24 01:54 CEST. Status: SOURCE CLEAR for the first compiler check. This review does not claim compiler acceptance. The reviewer did not author this candidate or run Lean.

The complete 125-line candidate is `/tmp/mcfta-cached-selection-20261024-canonical-union.lean`, SHA256 `2ea05def63d8d0bb4920e610b1c886d9b1d4202a64fd0e69959c6de4aacbc334`. The complete proposal is `/tmp/mcfta-cached-selection-20261024-union-realization-proposal.md`, SHA256 `c1f2ac7c77c8a0d30e416a744d49d84ccd11f5e13b6a7b877c9f609115160e24`.

No concrete type or proof error was found by static inspection. `merging_roots` derives the final representative map. It uses the actual winner path, `Merging.total`, the joined old classes, and `Merging.oldRoots`. It does not assume the desired final map. The selected branch identifies the actual endpoint with the winner. The unselected branch identifies its actual endpoint with its old representative.

The redirect fold equation permits any list order and repeated source keys. A redirect changes a selected value to the target. Later redirects retain that value. The explicit `keys` premise removes the winning key and describes the source set. The theorem does not claim to derive that premise from an executed native set conversion.

`terminal_transfer_correct` uses one supplied union-loop success and its consecutive winner lookup. `terminal_unions` and `merging_representative` provide the final `Merging` packet and winner path. `resolve_members` gives exactly the selected-list membership equation. The `forM_invariant` application uses its actual step-before-after argument order. Concrete union and representative readback retain the counter. `resolved.values` retains the complete old slot array. These facts establish the fixed-map frame before the existing count-transfer theorem changes the root map.

The endpoint contains the same full `after` core returned by the observed prefix. The transfer changes only its cached waiting table. No second execution, chosen winner, final root-map certificate, size-preservation premise, or semantic oracle was introduced. The input starts after the representative prescan. Prescan composition, native key-set realization, later assimilation, and full shared-driver correspondence remain separate obligations. No index invariant is asserted between the forest update and the completed count transfer.

The complete candidate and proposal were read. The following live cuts were also read for this review:

- `lean/MicroCFTA/EnumerationSchedule.lean`: 30–74, 205–232, 250–305, 430–590, 715–745, and 1030–1067. These cuts contain `Roots`, representative readback, `resolve_members`, `Merging`, the actual union-loop and winner interfaces, and `forM_invariant`.
- `lean/MicroCFTA/UnionFind.lean`: 35–52 and 268–296. These cuts contain terminal paths and the exact class-to-root equality interface.
- `lean/MicroCFTA/EnumerationPureSelection.lean`: 1–48 and 68–104. These cuts contain `Correct`, the actual transfer, and the frame and transfer proofs.
- `lean/MicroCFTA/EnumerationCanonicalWaiting.lean`: 30–55. This cut contains the canonical count predicate and literal redirect/move operations.
- `cfta/src/Data/CFTA/Enumeration.hs`: 720–752. This cut shows the representative prescan, actual unions, winner readback, deleted-winner key set, transfer, and subsequent assimilation.

Live identities at this review cut:

- `EnumerationSchedule.lean`: `3e84f2059725b3c0392d4df005574fde2918290cb393c4be0d549a62ad4a4e45`.
- `UnionFind.lean`: `3668867a41890e4721c301092a06c48d3bd757a8eede4b92340fe5db80119a14`.
- `EnumerationPureSelection.lean`: `32c3840fbade865c3e9342f6b7dddcc44fbfef0db0185b4950aedce3912e6729`.
- `EnumerationCanonicalWaiting.lean`: `a941b9b49e87115f26ecba015bc23e15a3d873410ac943ded77ff5f8963057bd`.

Only this report was written. No compiler, prepared tool, Git mutation, network operation, or repository edit was performed.
