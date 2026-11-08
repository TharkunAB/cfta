import MicroCFTA.SourceSynthesisJointProgramRequired
import MicroCFTA.SourceSynthesisNativeTypeSharedHeap
import MicroCFTA.SourceEqualityRequiredListFacts

/-!
# Shared Type facts at the actual Required return

The source constructor heap changes during requireAll. Its actual child
graph supplies physical effects, closed outputs and the conditional Mu
store. These facts advance the full checked state at that same heap.
Historical target slots and both warm Merge certificates remain valid.
Input positions distinguish Type operands from Program annotation fields.
Program guards need no Type annotation.

The successful Required observation and genuine initial classifications
remain premises. This law does not classify every reached operand or
derive a global bound, a future context, or native lazy demand order.
-/
namespace MicroCFTA.SourceSynthesisNativeTypeRequired
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceSynthesisTypeSyntax (Library)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceSynthesisTypePathRoles (AnnotationFields)
open SourceCurrentHereditaryProgramRequired (AnnotationOnly)
open SourceCurrentAllocatedSharedEditGraph (SharedState advanceHeap)
open SourceRecursiveIntersectionKernel (Extension)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Ready" => SourceSynthesisNativeTypeSharedState.Ready
local notation "Effects" => SourceCurrentConjunctionRowsAllocation.Effects
variable [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- Actual Required work retains shared readiness and every mixed operand classification. -/
theorem requireAll (lib : Library) (assigned : Nat → Prop)
    {fuel readFuel : Nat} {paths : List (List Int)} {entries : List (Int × SourceEqualityNeeded.Needed)}
    {values results : List (Value Symbol Guard)} {before : SharedState width} {heap : State Symbol Guard}
    (actual : SourceEqualityRequiredExecution.requireAll fuel readFuel paths values before.checked.native.machine.heap =
      .done results heap)
    (compiled : SourceEqualityNeeded.build paths = .node entries)
    (ready : Ready lib before) (available : Values before.checked.native.machine.heap values)
    (closed : ClosedValues values)
    (typed : ∀ index value, values[index]? = some value → ¬ assigned index → Annotated (Origin lib) value)
    (fields : ∀ index value, values[index]? = some value → assigned index → AnnotationFields (Origin lib) value)
    (only : ∀ (index : Nat) children, SourceEqualityNeededMap.lookup (index : Int) entries = some (.node children) →
      assigned index → AnnotationOnly children) :
    Ready lib (advanceHeap before heap) ∧
      Extension before.checked.native.machine (advanceHeap before heap).checked.native.machine ∧
      Values heap results ∧ ClosedValues results ∧ results.length = values.length ∧
      ∀ index value, results[index]? = some value →
        (assigned index → AnnotationFields (Origin lib) value) ∧ (¬ assigned index → Annotated (Origin lib) value) := by
  obtain ⟨constructors, length, classifications⟩ := SourceSynthesisJointProgramRequired.requireAll_slots
    (Origin lib) assigned actual compiled ready.checked.semantic ready.costs available closed
    ready.checked.stored.constructors typed fields only
  have graph := (SourceEqualityRequiredExecution.requireAll_execution_iff paths values
    before.checked.native.machine.heap results heap).mpr ⟨fuel, readFuel, actual⟩
  simp only [compiled] at graph
  have physical := SourceCurrentRequiredHeapEffects.children
    (SourceCurrentConjunctionEquality.FieldAvailable before.checked.operations) graph ready.checked.semantic ready.costs
    ready.checked.good.fields available
  have resultScope := SourceEqualityRequiredListFacts.children_verified graph ready.checked.semantic.ready available closed
  have effects : Effects (SourceCurrentAllocatedNativeEffects.physical before.checked)
      ⟨heap, before.checked.operations⟩ :=
    ⟨physical.1, ⟨physical.2.1, physical.2.2.1, ready.checked.good.operations, physical.2.2.2.1⟩,
      SourceEqualityConstraintMemoAllocation.grows_refl _⟩
  have nativeStore := SourceCurrentHereditaryNativeUniversalStore.advance (Origin lib) before.checked
    {before.checked.native.machine with heap := heap} ready.checked.stored constructors
  have nextReady : SourceSynthesisNativeTypeClosedRequests.Ready lib
      (SourceCurrentAllocatedQueryMemo.advancePhysical before.checked ⟨heap, before.checked.operations⟩) :=
    ⟨SourceCurrentAllocatedConjunctionMemo.advance_good before.checked _ ready.checked.good effects,
      physical.2.1,
      SourceCurrentAllocatedConjunctionMemo.advance_scoped before.checked _ ready.checked.scopes,
      SourceCurrentAllocatedConjunctionMemo.advance_idle before.checked _ ready.checked.idle, nativeStore⟩
  have extension := SourceCurrentAllocatedQueryMemo.advance_extension before.checked _ effects
  exact ⟨SourceSynthesisNativeTypeSharedState.advance lib before _ ready nextReady physical.2.2.1 extension,
    extension, physical.2.2.2.2, resultScope.2.2, length, classifications⟩

end MicroCFTA.SourceSynthesisNativeTypeRequired
