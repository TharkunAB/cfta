import MicroCFTA.SourceCurrentActualLocalRowOrigins

/-!
# Row origins from the actual allocated equality precheck

The initial raw constraint supplies the footprint. Its actual field load
and accessor derive coherent original records. The precheck orders those
records and the actual local class worker derives the surviving row origin.
No recursive root condition or future compiler fact is supplied.
-/
namespace MicroCFTA.SourceCurrentActualLocalReduceRowOrigins
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values)
open SourceCurrentActualRequiredRowOrigins (Link)
open SourceCurrentClassPositionalFootprints (Unselected)
open SourceCurrentNativeOperationHeap (Good)
open SourceCurrentMemoMergeEffects (Stored)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Record" => SourceEqualityClassOrder.Record
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "GuardHeap" => SourceCurrentConstrainedCapGuardHeap.Heap Plain
variable {width : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- Actual local reduction retains indexed row origins from the initial raw guard footprint. -/
theorem reduce {g s r e p h m c n budget loaded inherited values before fourth memo results after saved current}
    (actual : SourceCurrentAllocatedLocalWorker.reduce g s r e p h m c n budget loaded inherited values before fourth memo =
      .done results after saved current)
    (good : Good (width := width) before) (stored : Stored before.native.machine.heap memo)
    (original : Guard) (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (found : SourceEqualityConstraintFieldLookup.load original before.operations.constraints = .ok (some loaded))
    (inheritedReady : EqReady before.operations.constraints inherited)
    (available : Values before.native.machine.heap values) (guards : GuardHeap before.native.machine.heap)
    (index childIndex : Nat)
    (footprint : ∀ originals : List Record, SourceEqualityPhysicalPayload.own original = .ok (some originals) →
      ∀ record ∈ originals, Unselected record index childIndex)
    {source result : Node} (input : values[index]? = some source) (output : results[index]? = some result) :
    Link childIndex source result := by
  have field := SourceEqualityConstraintFieldLookup.load_ready original before.operations.constraints
    good.operations.constraints cached loaded found
  have constructor := SourceEqualityConstraintFieldLookup.load_constructor_receipt original before.operations.constraints cached loaded found
  obtain ⟨own,branch,ownRead,prefixDone,exact,valid,growth⟩ :=
    SourceEqualityPartialPrecheckAllocation.run_correct loaded.stored loaded.guard inherited before.operations
      good.operations field.1 inheritedReady original.equalities cached constructor
  have sameGuard : loaded.guard = original.guard := congrArg SourceSymbolicIndex.Constraint.guard field.2
  have ownRead : SourceEqualityPhysicalPayload.own original = .ok own.payload := by
    simpa only [sameGuard] using ownRead
  have effects : SourceCurrentConjunctionRowsAllocation.Effects (SourceCurrentAllocatedNativeEffects.physical before)
      ⟨before.native.machine.heap,(SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard inherited before.operations).2⟩ :=
    ⟨SourceEqualityRequiredCache.pure_keeps _ good.heap,
      ⟨good.semantic,good.costs,valid,good.fields.grows growth⟩,growth⟩
  have currentGood := good.advance _ effects
  simp only [SourceCurrentAllocatedLocalWorker.reduce,prefixDone] at actual
  cases branch with
  | unchanged =>
    cases actual
    have same : result = source := Option.some.inj (output.symm.trans input)
    cases same
    exact Link.refl _ _
  | emptyChildren =>
    cases actual
    have member : result ∈ values.map (fun _ => (Value.empty : Node)) := List.mem_of_getElem? output
    obtain ⟨value,included,same⟩ := List.mem_map.mp member
    cases same
    intro row impossible
    cases impossible
  | classes records =>
    have entry := (SourceEqualityPhysicalClassEntry.entry_of_own original inherited.payload own.payload ownRead).trans exact
    obtain ⟨originals,read,classes,checked,ordered,coherent⟩ :=
      SourceEqualityPhysicalClassEntry.live_records original cached inherited.payload records entry
    have unselected : ∀ record ∈ records, Unselected record index childIndex := by
      rw [ordered]
      intro record member
      exact footprint originals read record ((SourceEqualityClassOrder.ordered_perm originals).mem_iff.mp member)
    exact SourceCurrentActualLocalRowOrigins.classes actual currentGood (stored.grows effects.keeps)
      (fun value member => effects.keeps.available value (available value member)) guards
      (fun record member => (coherent record member).1) index childIndex unselected input output

end MicroCFTA.SourceCurrentActualLocalReduceRowOrigins
