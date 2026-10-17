# Independent review of complete Scan and Required preparation

Reviewed 2026-10-17. Final source: `SourceCurrentScanRequiredNumeric.lean`, SHA256 `24534bc63167c1ef51074234e81e3a2193f04eac1799726f6bbe7a749759c916`. The root strict attempt 4 has an empty log. The canonical target passes 1716 jobs. This review changes no production source.

## Result and initial premises

No material defect was found. `complete` constructs the actual prefix from initial Context, same-inventory Frame, profile Fits, available original values, proper paths, coherent and active original records, and the initial Scan Reserved schedule. It does not take an actual Scan, Required graph, selected record list, reached heap bound, successful future worker equation, Ranges, finite input Cap, or whole-forest closedness as an initial premise. Context and Frame retain the physical and semantic cache laws. Those initial invariants remain explicit; this theorem does not initialize them for arbitrary stores.

The public execution has two source branches. A stopped Scan erases the original forest and skips Required. A successful Scan uses the exact kept original records, the original forest, the checked state returned by Scan, and that Scan's fourth memo. Required advances only the heap of that literal checked state. The strict Reads graph threads the exact Scan-returned global bundle into Required.

The numeric entry forecast first schedules Scan from the original guard carrier and original records. `SourceCurrentInitialSelectionForecast.selections` enumerates positional sublists. It does not discard repeated records. Its complete membership theorem maps the actual retained Sublist to this initial finite enumeration. Joining the Required profile of each enumerated sublist bounds the actual Required forecast. The forest count stays equal to the original count. The common fuel is the maximum of the initial Scan fuel, all enumerated Required worker fuels, and the reader bound of the joined Required profile. Thus no later selected list is needed to choose the initial profile or fuel. The definitions remain logical, partly noncomputable bounds; this is not an extracted runtime budget.

## Exact source and semantic alignment

The Scan call returns original record occurrences through `Retained`; equality of path projections alone does not identify duplicate records. `RecordScanNumeric.retained_run` uses full record-worker uniqueness to recover the exact retained list. The resulting Sublist preserves source order and multiplicity.

In the stopped branch, the receipt returns the exact Scan state and saved fourth memo. Available erased values and forest length follow from the original slots. The rejected class has the old stopped-soundness contract. Erased forest language narrows the original language. Under satisfaction of all original records, the sound rejected class makes the preservation direction vacuous. No unused suffix or Required execution is asserted.

In the successful branch, `ConjunctionRequired.selected_primary` derives the anchored original false primary certificates from this Scan and its derived Ranges. `RequiredInitialNumeric.caller` constructs Required without Caps. Its causal GuardHeap comes from actual Required reads, not from an assumed Cap on every original root. The returned Frame and Post use the same actual next inventory. Post composition retains the full checked state, outer result tables, unchanged Merge memo, fourth history, probe heap, and valid global bundle at the exact Required return.

The selected endpoint domains come from the full Required receipt. They apply to every original path occurrence in each kept record. Terminal tips and non-maximal selected prefixes are retained. Unselected open ordinary siblings remain allowed. This does not admit arbitrary open recursive heads on selected paths.

The language result states narrowing for every accepted returned forest. It also states equivalence with the original forest when all original records hold. The successful branch combines the actual Required language theorem with satisfaction of the kept sublist. It does not assume nonemptiness from a false memo answer.

`Receipt.run` permits all six preparation fuels to grow independently. Scan uses g/s/p/h/n. Required uses r/h. The shared reader parameter h covers both stages. The stopped branch does not need r. Worker stability fixes the exact returned forest, complete checked state, fourth memo, and Merge memo; it is not only an equality of languages.

## Literal worker boundary

The separately pinned `SourceCurrentScanRequiredWorker.classes` proves a definitional factorization of the old complete class worker through this preparation. It covers Scan failure and Required failure as well as both successful branches. The stopped branch returns the erased forest. The successful branch still calls the old class pass on the prepared forest. The theorem does not construct that class pass. Therefore the full uncapped Local worker remains open. The uncapped Target producer is available, but uncapped Force, Leaf, finite editor scans, Class, and ClassPass numeric composition remain to be proved. Existing capped endpoints do not close that gap for arbitrary supported non-Cap inputs.

## Imported coverage

The final immutable probe is `prefix-final-review-public-2.source.lean`, with raw log `prefix-final-review-public-2.log`. It checks 22 distinct heads: four handwritten public declarations, all 14 Receipt field projections, both Execution constructors, and both Reads constructors. Every head has a full explicit signature, axiom report, and declaration/proof print. Only propext, Classical.choice, and Quot.sound occur. There are no diagnostics or printer omissions.

The first immutable probe also compiled successfully. It is retained as a formatting attempt. Lean's `#print` implementation disables `pp.proofs` for structure field summaries and omitted the dependent `Receipt.actual` argument once. The final probe sets `pp.proofs.threshold` to 254. This exposes that field in the structure summary. No source theorem or linter setting changed. Constructed branch integrations belong to the separate parent-owned integration component and are not counted here.
