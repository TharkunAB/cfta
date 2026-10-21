# Raw endpoint corridors through chronological class folds

Date: 2026-10-21 05:13 CEST.
This plan has zero Lean jobs and zero new proof pairs.
The fold, pass and indexed-phase statements below are not yet proved.
The per-class dependency was proposed when this investigation started.
Its final 420-line source now has SHA-256 bc0701959646a61bee767cf6b80db04b314302d16891efd7aa539ca314eacd84.
Root reports its strict check and default Audit pass.
This package does not add a check of that dependency.

## Minimal fold statement

Use a new additive module.
Do not change the frozen per-class, raw-corridor or old class-pass modules.
Use one private universal relation:

```lean
Preserves original result :=
  ∀ path : List Int, RawCorridor path original → RawCorridor path result
```

Keep this relation expanded in every public type.
No public E-mask structure or historical invariant is needed.
The proposed `fold` takes the SAME actual Fold and FoldReads.
It takes the same initial facts as AllocatedClassPass.Fold.verified.
It adds initial CurrentNative.At Plain, conditional MergeStored Plain and raw masks for every record path.
Its full shape is:

```lean
(reads : FoldReads formulas solver actual memos final)
(coherent : ∀ record ∈ records, Coherent record)
(active : ∀ record ∈ records, Nontrivial record.paths)
(ready : Ready before)
(admitted : At formulas solver inventory before)
(available : Values before.native.machine.heap values)
(domains : ∀ record ∈ records, ∀ path ∈ record.paths,
  ForestClosed (path.map Int.ofNat) values)
(physical : PhysicalStored before.native.machine.heap memo)
(covered : ∀ ambient, CacheCovers (holds formulas solver) ambient memo)
(valid : GlobalValid before.native.machine.heap memos)
(current : CurrentNative.At Plain before)
(merged : MemoMerge.Stored Plain memo)
(masks : ∀ record ∈ records, ∀ index path,
  index :: path ∈ record.paths → ∀ value,
    select values (Int.ofNat index) = some value →
      RawCorridor (path.map Int.ofNat) value)
:
∃ next, AllocatedClassPass.Receipt formulas solver next records
  values before memo results after saved memos final ∧
  CurrentNative.At Plain after ∧ MemoMerge.Stored Plain saved ∧
  All₂ (fun original result =>
    ∀ path, RawCorridor path original → RawCorridor path result)
    values results
```

Here actual has type `Fold records values before memo results after saved`.
There is no full cap on every value and no false gate on changed values.
The relation preserves every initial raw corridor, including corridors for paths outside the processed tail.
Thus it preserves all originally selected E paths without an extra E parameter.
The masks premise supplies placement only for actual edit paths.

## Tail-first proof

Follow FoldReads.cons and the literal Fold.cons order.
First apply the induction hypothesis to the actual tail.
It returns Current and MergeStored at the exact middle state and memo.
It also returns All₂ Preserves from the original entry values to the actual middle values.

Obtain the old Receipt for THAT actual tail through Fold.verified.
Use receipt.ready, admitted, available, stored, covered and globals.valid at the head entry.
For each head path, use receipt.domains on the original head domain.
Use all₂_signed on the tail relation to retain the same forest index.
Apply its value relation to the ORIGINAL head mask.
This derives the head mask on the literal tail-produced middle forest.
Then invoke ClassEndpointCorridors.class_reads on the SAME head reads.
Compose the two ordered universal relations.
Do not replace middle with the prepared forest.

MixedClassPass.fold_caps, line 53, is the existing checked proof template.
It reuses public Fold.verified to obtain tail support instead of importing the private cons_receipt.
The new proof can use the same access pattern.
A final public Fold.verified call retains the complete actual fold Receipt.
No operation is re-executed by these proof applications.

## Final propagation and indexed phases

The proposed `pass` consumes actual PassReads.
It applies the fold theorem to the SAME contained fold.
Literal empty propagation either keeps every value or maps every position to Empty.
Empty has a finite zero cap and therefore every raw corridor.
A private ordered relation proof composes that pure propagation with the fold relation.
The checked state and memo are unchanged by propagation.
Pass.verified supplies the complete receipt at the exact returned forest.

The proposed `indexed_phase` starts with records[index]? = some record.
Call ClassPassPhaseLineage.fold_indexed once.
Retain its SAME tail, class call, later fold, all three reads and exact drop/take record schedules.
Apply the new fold theorem once to THAT tail.
Its receipt yields the actual phase inventory, readiness, admission, Values, physical Stored, covered and global validity.
Its new fields yield Current and MergeStored at the SAME phase state and memo.
Its All₂ relation retains all original E corridors in the SAME phaseValues.
An all₂_signed step derives any requested phase mask.
No initial or final native History is required for these facts.
Do not use fold_phase solely to obtain them: that endpoint adds a History premise for separate conclusions.
No unique phase or inventory is claimed.

## Actual entry producers

Retained.fields in ConjunctionSelectedRecords, line 73, gives the exact selected record path list and original sublist.
Retained.live_retained_records, line 146, supplies coherence and nontriviality from the actual live class accessor.
The actual retained order already matches the class pass.
If sorting precedes Scan, ClassOrder.ordered_perm and ordered_coherent transport membership and coherence.
Do not identify a sorted list with an unsorted list by equality.

ConjunctionRequired.selected_primary, line 35, derives ORIGINAL false ClassTrace receipts at the actual Scan return.
RequiredRawCorridor.required then consumes the literal actual requireAll and initial semantic, UnionNormal, cost, Values and Plain guard-heap facts.
Its same-index result supplies each initial prepared mask.
Use Retained.fields' exact selected-list equation to choose the corresponding original class.
Do not derive UnionNormal or a Plain guard heap from arbitrary Good.

ConjunctionRequiredActual.verified, line 40, identifies the supplied actual Required return with its complete Required receipt.
That receipt gives ready, admitted and resident prepared values.
ConjunctionRequiredClassPass.selected_domains, line 29, derives all initial class domains from its paths field and the exact selected-list equation.
For every later phase, the actual tail Receipt.domains transfers those original domains forward.
Raw corridors and ForestClosed remain separate predicates.

Initial Current and conditional MergeStored remain genuine entry premises of the core theorem.
They do not follow from the physical Fold Receipt alone.
If an integration adapter starts before Required, CurrentNative.advance can reuse the actual unchanged native cells, extension, final semantic readiness and a genuinely preserved Plain guard heap.
Required receipts expose nodes, edges and extension for this purpose.
The conditional Merge law is unchanged when its memo is unchanged.
This adapter is separate from the small fold proof.
Current support must never be used to infer a past writer-entry law.

For a literal successful worker instead of supplied FoldReads, ActualClassSemanticReads.fold_reads, line 64, is the existing producer.
It uses an initial Frame, Fits, numeric Reserved, Values, domains, physical Stored, covered and global validity.
Worker return uniqueness fixes the SAME values, state and memo.
Raw successful worker equations alone do not supply all semantic reads or capacity facts.
The new fold theorem should consume the resulting actual reads rather than add a new admission or range framework.

## Scope and size

The initial implementation should have three public heads: fold, pass and indexed_phase.
Keep universal relation composition, mask selection and final propagation private.
The target size is 220–260 lines.
The actual per-class endpoint is a dependency, not a caller-supplied desired result law.
All old proof bytes remain unchanged.

This proves a chronological finite-endpoint corridor invariant for completed actual class folds and their exact internal phase cuts.
It does not prove future class/native completion, opaque-Mu positive observation ancestry, NormalizedChildSeparation.Rel, retained-owner exclusion, renewal, termination or Haskell refinement.
It does not claim internal failed worker states or arbitrary execution prefixes.
