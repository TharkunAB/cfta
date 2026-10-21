import MicroCFTA.SourceCurrentResourceParentWriters
import MicroCFTA.SourceCurrentActualParentBranchCases
import MicroCFTA.SourceCurrentActualParentSelectedCertificates

/-!
# Closed children from the same historical Parent writer

The literal Parent return retains closed children of its captured request.
The selected branch uses the same Required return and class pass.
-/
namespace MicroCFTA.SourceCurrentResourceParentClosed
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard

private theorem required_closed [DecidableEq (EdgeKey Symbol Guard)]
    {fuel readFuel : Nat} {paths : List SourceEqualityNeeded.Path}
    {values results : List Node} {before after : InternedConstructorTemplates.State Symbol Guard}
    (actual : SourceEqualityRequiredExecution.requireAll fuel readFuel paths values before = .done results after)
    (ready : SourceEqualityRequiredCache.Ready before) (available : Values before values)
    (closed : ClosedValues values) : ClosedValues results := by
  obtain ⟨chosen, heap, _keeps, _available, chosenClosed, bound, readBound, stable⟩ :=
    SourceEqualityRequiredExecution.requireAll_complete paths values before ready available closed
  obtain ⟨same, _⟩ := SourceCurrentConjunctionRequiredActual.required_unique
    (stable bound readBound (Nat.le_refl _) (Nat.le_refl _)) actual
  exact same ▸ chosenClosed

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
  [DecidableEq Node] {bits : Nat}

/-- The same historical Parent return preserves closed captured children. -/
theorem children
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {request : SourceCurrentAllocatedPartialState.EdgeRequest}
    {returned : EdgeValue Symbol Guard}
    (written : SourceCurrentResourceParentWriters.Written (bits := bits) formulas solver request returned)
    (closed : MergedColdReaderClosedInputs.ClosedValues request.value.children) :
    MergedColdReaderClosedInputs.ClosedValues returned.children
 := by
  obtain ⟨g,s,r,e,p,h,m,c,n,budget,writerBefore,writerAfter,savedFourth,savedMerge,
      globals,inventory,profile,observed,context,frame,fits,inheritedReady,_resident,
      liveInputs,reserved,normal,supported,⟨causal⟩,_merged,_positiveMemo⟩ := written
  have nativeGood := SourceCurrentNativeOperationHeap.Good.of_native
    (SourceCurrentNativeOperationInvariants.Good.of_checked context.ready.good)
    context.ready.semantic context.ready.costs
  rcases SourceCurrentActualParentBranchCases.edge_cases observed nativeGood context.stored liveInputs with
      unchanged | erased | sentinel | selected
  · simpa only [unchanged] using closed
  · intro value member
    rw [erased] at member
    obtain ⟨_,_,rfl⟩ := List.mem_map.mp member
    rfl
  · intro value member
    rw [sentinel] at member
    have same : value = .empty := List.mem_singleton.mp member
    subst value
    rfl
  · obtain ⟨loaded,_middle,records,kept,scanned,scanFourth,preparedValues,preparedHeap,
        noncontradictory,loadedAt,_reduced,_built,_accepted,precheck,scanCall,_nonempty,
        requiredCall,passCall,_sameFourth⟩ := selected
    obtain ⟨fieldAt,_inherited,available⟩ := liveInputs noncontradictory
    have parentLive : SourceCurrentParentNumeric.LiveInputs request.value.entry.key.constraint loaded
        request.inherited request.value.children writerBefore :=
      fun _ => ⟨fieldAt.1,loadedAt,inheritedReady,available⟩
    have parentReserved : SourceCurrentParentForecast.Reserved bits budget request.value.children.length
        request.value.entry.key.constraint loaded request.inherited writerBefore.checked profile := by
      simpa only [SourceCurrentParentForecast.residentReserved,noncontradictory,
        Bool.false_eq_true,ite_false,loadedAt] using reserved
    obtain ⟨_next,final,_own,preparedInventory,scanMemos,preparedMemos,_numeric,_trace,retained,
        _pass,_assembled,precheckReceipt,_scanReads,_requiredReads,passReads,requiredReceipt,
        preparedValid,scanReady,scanEffects,_extension,scanValues,_scanCurrent,_scanSupport,
        _scanHistory,_scanNormal⟩ :=
      SourceCurrentActualParentSelectedCertificates.selected_certificates formulas solver inventory budget
        request.value.entry.key.symbol request.value.entry.key.constraint loaded request.inherited
        request.value.children writerBefore globals context frame profile fits parentLive parentReserved observed
        noncontradictory precheck scanCall requiredCall passCall normal supported causal
    have preparedClosed : ClosedValues preparedValues :=
      required_closed requiredCall scanReady.semantic.ready scanValues closed
    obtain ⟨_proper,_raw,_rawRead,_sourceClasses,_order,recordFields⟩ := precheckReceipt.classes records rfl
    have retainedFields := retained.fields
    have coherent : ∀ record ∈ kept, SourceEqualityClassOrder.Coherent record :=
      fun record member => (recordFields record (retainedFields.1.subset member)).1
    have active : ∀ record ∈ kept, EqualityNormalize.Nontrivial record.paths :=
      fun record member => (recordFields record (retainedFields.1.subset member)).2.2
    have domains : ∀ record ∈ kept, ∀ path ∈ record.paths,
        SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) preparedValues := by
      intro record member path included
      exact requiredReceipt.paths path (List.mem_flatten.mpr
        ⟨record.paths, List.mem_map.mpr ⟨record,member,rfl⟩, included⟩)
    have preparedStored : SourceCurrentMemoMergeEffects.Stored preparedHeap writerBefore.merge :=
      (context.stored.grows scanEffects.keeps).grows requiredReceipt.effects.keeps
    obtain ⟨_finalInventory, receipt⟩ := SourceCurrentAllocatedClassPass.Pass.verified formulas solver
      preparedInventory passReads coherent active requiredReceipt.ready requiredReceipt.admitted
      requiredReceipt.resident domains preparedStored context.covered preparedValid
    exact receipt.domains [] preparedClosed

end MicroCFTA.SourceCurrentResourceParentClosed

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#check @MicroCFTA.SourceCurrentResourceParentClosed.children
#print MicroCFTA.SourceCurrentResourceParentClosed.children
#print axioms MicroCFTA.SourceCurrentResourceParentClosed.children
