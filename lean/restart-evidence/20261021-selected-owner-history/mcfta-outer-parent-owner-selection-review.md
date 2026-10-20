# Independent final Parent history and owner-selection review

Reviewed 2026-10-21 01:42 CEST. No material issue found. This review ran zero Lean jobs, edited no production source, and left the historical b7ca5c78 review and all frozen components unchanged.

Final sources:

- `SourceCurrentOuterParentHistory.lean`: `9c238d8c19b5e6cfa4f1f358d0d38c4b29ce7c9e5355ebcd87ff1cbe9a7640b0`, 373 lines.
- `SourceCurrentOuterOwnerSelection.lean`: `2ff2289d0bf693131f1455939c5d5c16742a034e3d94e189b3e3bf4fa1b6b9e8`, 104 lines.

The ParentHistory source differs from the independently read b7ca5c78 source only in the corrected `reached` comment. Replacing that one comment reproduces the exact old hash. Its proof still records the actual complete Parent execution at cold finish and recovers its exact captured request at a warm hit. Lookup/demand and completed earlier calls preserve the certificate. The unfinished-prefix theorem needs no enclosing future return. Empty initialization supplies Origins; arbitrary supplied warm tables retain that explicit premise.

The new `OuterOwnerSelection.selected` first uses the SAME actual edgeCall to derive the current physical Good/effect and returned edge residency. Initial active-cell readiness makes the complete ordinary owner available before the call. Actual effects retain it at the returned reader. The returned edge's cached children make the selected literal child available at that SAME reader. Coherent physical reference injectivity therefore derives `child = owner.value`. It does not infer whole-value equality from reference equality in different heaps.

The exact selected index is retained while replacing the child by the derived full ordinary owner. The theorem obtains the Parent writer once from the same edgeCall and Origins. It unpacks this writer once, retains its full request/result, checked endpoints and both memos, and passes THAT execution plus the SAME child lookup and original row membership to `ActualOwnerSelection.selected`.

The core selection law eliminates unchanged children by the pure structural child-mass inequality. Erasure and sentinel outputs cannot contain the ordinary owner. This argument needs no owner availability at the historical writer's entry. The remaining branch retains the actual nonempty selected list, accepted constructor, local return, Scan return, Required return and class-pass return. It keeps the writer's original child forest for every false primary ClassTrace at the writer's final Scan heap. It never transfers a false gate to the prepared or edited forest.

The checked dependencies include the complete ActualOwnerSelection proof, the actual Parent branch decomposition, current coherent reference equality, physical edge effects, and the selected-record false-primary producer. Parent reports the new selection module's canonical build as terminal0; this review does not own or rerun that check.

The conclusions do not export a writer-to-current-reader heap interval, chronological cache-event membership, writer uniqueness, or equality of historical/current execution bounds. They do not derive a retained same-child pair from the nonempty selected list. The selection premise is an exact literal returned child occurrence with equal owner reference; the result does not classify every possible observation or prove a global renewal rank. No future outer completion or Haskell refinement is claimed.
