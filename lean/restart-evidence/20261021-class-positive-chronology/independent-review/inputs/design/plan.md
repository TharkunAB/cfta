# Positive ancestry through the actual class right fold

Status: SOURCE-ONLY PLAN. The proposed chronology result is unproved. This package runs zero Lean commands and changes no official source.

The next useful producer is chronological positive ancestry for a completed `FoldReads` and its completed `PassReads`. The single-class theorem now returns the native positive store, causal publication history, and Merge positive store at its exact return. A fold induction can pass those actual returns into the next class. It does not need a supplied output-origin callback or a historical writer law. [R1, R2]

## Proposed public scope

Use one new additive module, provisionally `SourceCurrentClassPositiveChronology`. Expose `fold` and `pass`. Keep the exact arguments of the corresponding `ClassCorridorChronology` endpoints. Add only these genuine entry laws:

```lean
(supported : NativeSupport before.native.machine.heap before.native)
(causal : History empty before.native.machine.heap)
(positiveMemo : MergeSupport memo)
```

`History` is `SourceCurrentNativeMuPublication.History`. It is not `NativeEdgeWriterGrowth.History`. No native writer history or final history is inferred from heap growth. [R1, R6]

Return the existing actual pass/fold `Receipt`, current cap/origin store, Merge cap store, and ordered raw-corridor relation. Also return native positive support, nonempty causal history to the same final heap, Merge positive support, and this backwards law:

```lean
∀ outputIndex result, results[outputIndex]? = some result →
∀ residual, PositiveAt result residual →
  ∃ inputIndex originalPath original,
    values[inputIndex]? = some original ∧
    PositiveAt original originalPath ∧
    Rel (records.map Record.paths)
      (outputIndex :: residual) (inputIndex :: originalPath)
```

The full proposed signatures are in `proposed-signatures.lean.txt`. The text has no proof and was not compiled. No normalization fixed-point premise is needed to construct `Rel`. A later use of `single` or `child_separate` has stronger, separate premises. Do not add an indexed public theorem before a consumer needs it. The proposed `fold` can already apply to the actual tail returned by `fold_indexed`. [R3, R6]

## Exact entry facts remain explicit

Retain coherent, nontrivial records; entry `Ready` and inventory admission; available entry values; domains for all selected paths; physical Merge `Stored`; language `CacheCovers`; global memo `Valid`; current cap/origin store; conditional Merge cap store; and the original entry raw masks for every selected record. Add the three laws above. Neither availability nor physical storage implies a warm positive cache law. No all-root cap is needed. [R1, R2]

The captured forest of each class is its literal completed tail return. The theorem's final source forest is the entry forest of the whole fold. The two forests need not be equal. No false gate is imposed on a changed phase capture. [R2, R4]

## Private proof route

Adapt the existing `ClassCorridorChronology.fold_law` induction. Keep all helpers private. A private relation-weakening helper is enough: class-family membership inclusion transports a `Rel` proof by induction on `refl`, `member`, and `trans`. This is finite path geometry, not an execution-origin premise. [R2, R3]

1. For `FoldReads.nil`, preserve the exact state and all stores. The positive witness is the same slot and residual; use `Rel.refl`.
2. For `FoldReads.cons`, first apply the tail induction to its actual `first` receipt. Its conclusion supplies native support, causal history, Merge support, and positive ancestry at the exact `middle/step/current/stepMemos` cut.
3. Obtain the other facts at that same cut from `Fold.verified` on the actual tail. Its receipt supplies readiness, inventory admission, available tail values, physical Merge storage, language coverage, and global memo validity. Its `domains` field transports the original selected domains. Use the tail's ordered corridor relation and `all₂_signed` to transfer this head record's original masks. This is the existing chronology route. [R2, R4]
4. Call `ClassPositiveAncestry.class_reads` once for the actual head. Pass the tail's derived current stores and three new laws. Unpack its positive result: a returned positive position reaches one positive occurrence in the actual tail capture.
5. Apply the tail's backwards law to that exact intermediate slot, value, and path. Its selected lookup is the one returned by the head law. No independently selected occurrence is needed.
6. Embed `Rel [record.paths]` into the full family using head membership. Embed the tail relation into the same family using tail membership. Compose head-to-middle with middle-to-entry using `Rel.trans`. The complete intermediate path is identical in the two proofs. [R1, R3]
7. Retain final cap stores and ordered raw corridors as in the old fold. A public wrapper can reuse the old public endpoint on the same actual reads to supply its existing receipt. No receipt identity or inventory uniqueness claim is needed.
8. For `PassReads.done`, use the fold result before final empty propagation. `propagate` changes no state or memo. If it erases the forest, every returned slot is literal Empty and has no `PositiveAt` constructor. Otherwise use the unchanged fold result. Do not postulate positivity after propagation. [R4, R7]

The main new work is the composition in steps 4–6 and threading the actual three laws. It does not need another node/edit induction or another cap/exposure proof. Estimate 190–260 lines including imports, exact signatures, private path weakening, positive propagation, and two public wrappers. Review the scope if dependent receipt elaboration pushes this beyond roughly 300 lines.

## Indexed phase captures need no new history premise

For a selected source occurrence, `ClassPassPhaseLineage.fold_indexed` returns the actual `drop (index+1)` tail, same class call, and actual `take index` remainder with their exact states and memo bundles. Applying the proposed `fold` to that returned tail gives the three laws and backwards relation at the actual phase capture. Restrict coherent/active/domain/mask premises by drop membership. This needs no caller-supplied phase support and no current-to-past support inference. [R6]

The old `fold_phase` endpoint uses a different native writer history. It remains useful for its stated scope, but is not the producer of the causal history or positive stores needed here. The proposed tail induction is the producer of those laws. [R6]

## Actual Required entry is a later small adapter

The 89-line `RequiredCorridorChronology.pass` already shows how to derive initial masks and domains from one actual Required receipt. Unpack `required.stable` at its own bounds; apply `RequiredRawCorridor.required` to that literal successful `requireAll`; use `selected_domains` for the same returned forest and prepared checked state. Keep scan semantic/normal/cost/available/GuardHeap Plain and ORIGINAL false class traces explicit. [R5, R8, R9]

For positive ancestry back from the prepared forest to the original forest, `RequiredForestPositive.requireAll` already preserves the same forest slot and natural path under those same actual Required and original-gate premises. Therefore no new Required-origin induction is needed. A later adapter can compose the fold's entry positive witness with that public theorem while retaining the same `Rel` endpoint path. It must still receive genuine prepared current/native/Merge laws or derive them from actual preceding operations. The old Required adapter does not supply those new warm laws. [R5, R10]

The selected class family is not automatically the whole normalized family. Actual `Retained.fields` gives the kept records' sublist and exact selected path list. `Retained.input` gives the original record-path list. These facts can justify a later `Rel` weakening into the original normalized class family. Do not assume selected classes are a congruence fixed point. [R11]

## Common-anchor boundary remains real

`NormalizedChildSeparation.child_separate` requires `Rel classes (index::left) other` and `Rel classes (index::right) other` with ONE identical `other`. It also needs the actual normalized fixed point and the dropped-class condition through that child. The proposed chronology returns one source witness for each positive output. Those witnesses can differ. It does not create a common anchor. [R3]

Structural reasoning, not a new Lean counterexample: take `classes=[]` and an identity fold with two positive ordinary positions under one root, such as paths `[i,0]` and `[i,1]`. `Rel []` contains only equality through reflexive/transitive proofs. The two backwards witnesses can be their distinct entry paths. Positivity of both positions gives no relation of both to one path. This rules out the inference from two independent existential ancestry results to the common-anchor premise. It is not a runtime defect or an actual-owner-repeat counterexample. [R3, R12]

A later actual-owner argument must connect its two selected occurrences to the same original occurrence, or supply another actual relation between the two entry anchors. Bare interned reference equality does not choose one source occurrence. No such common-anchor producer follows from the cited class/corridor endpoints. This plan does not invent it as an input callback.

This plan proves no common anchor, active-owner exclusion, dropped-class transport, future class return, failed-prefix preservation, global renewal, termination, or Haskell refinement. The only proposed implementation is the completed fold/pass chronology above.

## Source map

The exact whole-file hashes and selected line ranges are in `source-pins.json` and `ranges.json`. All source snapshots use ROOT-relative paths.

- R1: `SourceCurrentClassPositiveAncestry.lean` 434–486. The installed file and the author's final source have the same SHA `71171ea0e0a9068adac8bce73ca5228b967d305489da61fa0f7de6284f1e0842` at review time. This plan does not count their checks as its own.
- R2: `SourceCurrentClassCorridorChronology.lean` 28–70, 72–156, 159–195.
- R3: `SourceCurrentNormalizedChildSeparation.lean` 15–24, 88–96, 118–145.
- R4: `SourceCurrentAllocatedClassPass.lean` 33–101, 150–172, 208–239.
- R5: `SourceCurrentRequiredCorridorChronology.lean` 38–87.
- R6: `SourceCurrentClassPassPhaseLineage.lean` 28–63, 65–137.
- R7: `EqualityLeafProjectionRuntimeEmpty.lean` 21–25.
- R8: `SourceCurrentRequiredRawCorridor.lean` 91–118, 176–218.
- R9: `SourceCurrentConjunctionRequired.lean` 107–126; `SourceCurrentConjunctionRequiredClassPass.lean` 29–40.
- R10: `SourceCurrentRequiredForestPositive.lean` 29–58.
- R11: `SourceCurrentConjunctionSelectedRecords.lean` 73–101, 146–160.
- R12: `SourceCurrentRequiredPositivePosition.lean` 25–41.
