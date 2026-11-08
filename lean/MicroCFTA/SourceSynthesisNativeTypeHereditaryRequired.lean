import MicroCFTA.SourceSynthesisHereditaryProgramRequired
import MicroCFTA.SourceSynthesisNativeTypeRequired

/-!
# Recursive Program fields at the actual Required return

Assigned slots retain their full recursive Program fields. Other slots
retain their complete Type annotation. The actual ordered child graph
supplies the intermediate physical facts and the conditional Mu store.
The checked native wrapper retains historical targets and warm memos.

Successful execution, initial operand classifications, and annotation-only
Program footprints remain premises. These laws do not prove completion,
failed-prefix safety, all reached classifications, or a global bound.
-/
namespace MicroCFTA.SourceSynthesisNativeTypeHereditaryRequired
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityNeeded (Needed)
open SourceEqualityRequiredGraph
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceCurrentHereditaryConstruction (MuStored)
open SourceCurrentHereditaryProgramRequired (AnnotationOnly)
open SourceSynthesisHereditaryProgramFields (ValueFields)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

section Generic
variable {Symbol : Type} [DecidableEq (EdgeKey Symbol Guard)]

private def Slot (valid : Guard → Prop) (literal : String → Symbol)
    (assigned : Nat → Prop) (index : Nat) (value : Value Symbol Guard) : Prop :=
  (assigned index → ValueFields valid literal value) ∧ (¬ assigned index → Annotated valid value)

private theorem mixed_children (valid : Guard → Prop) (literal : String → Symbol) (assigned : Nat → Prop)
    {entries : List (Int × Needed)} {offset : Nat} {values results : List (Value Symbol Guard)}
    {before after : State Symbol Guard} (actual : RequireChildren entries offset values before results after)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Values before values) (closed : ClosedValues values) (stored : MuStored valid before)
    (inputs : ∀ index value, values[index]? = some value → Slot valid literal assigned (offset + index) value)
    (only : ∀ (index : Nat) children, SourceEqualityNeededMap.lookup (index : Int) entries = some (.node children) →
      assigned index → AnnotationOnly children) :
    MuStored valid after ∧
      ∀ index value, results[index]? = some value → Slot valid literal assigned (offset + index) value := by
  classical
  induction values generalizing offset before results after with
  | nil =>
      cases actual
      refine ⟨stored, ?_⟩
      intro index value found
      simp only [List.getElem?_nil] at found
      cases found
  | cons value values ih =>
      have headInput : Slot valid literal assigned offset value := by
        simpa only [Nat.add_zero] using inputs 0 value rfl
      have tailInputs : ∀ index child, values[index]? = some child →
          Slot valid literal assigned (offset + 1 + index) child := by
        intro index child found
        simpa only [Nat.add_assoc, Nat.add_comm 1 index] using inputs (index + 1) child found
      cases actual with
      | unselected offset absent rest =>
          obtain ⟨kept, returned⟩ := ih rest semantic costs
            (fun child member => available child (List.mem_cons_of_mem _ member))
            (fun child member => closed child (List.mem_cons_of_mem _ member)) stored tailInputs
          refine ⟨kept, ?_⟩
          intro index child found
          cases index with
          | zero =>
              cases Option.some.inj found
              simpa only [Nat.add_zero] using headInput
          | succ index =>
              simpa only [Nat.add_assoc, Nat.add_comm 1 index] using returned index child found
      | selected offset found first rest =>
          have request : ∀ (needed : Needed) (result : Value Symbol Guard) (middle : State Symbol Guard),
              RequireNode needed value before result middle →
              SourceEqualityNeededMap.lookup (offset : Int) entries = some needed →
              MuStored valid middle ∧ Slot valid literal assigned offset result := by
            intro needed result middle call selected
            cases needed with
            | node children =>
                by_cases program : assigned offset
                · obtain ⟨kept, returned⟩ := SourceSynthesisHereditaryProgramRequired.node valid literal call semantic costs
                    (available _ List.mem_cons_self) (closed _ List.mem_cons_self) stored (headInput.1 program)
                    (only offset children selected program)
                  exact ⟨kept, fun _ => returned, fun excluded => False.elim (excluded program)⟩
                · obtain ⟨kept, returned⟩ := SourceCurrentHereditaryRequiredMerge.node valid call semantic costs
                    (available _ List.mem_cons_self) (closed _ List.mem_cons_self) stored (headInput.2 program)
                  exact ⟨kept, fun selected => False.elim (program selected), fun _ => returned⟩
          have firstResult := request _ _ _ first found
          have effects := SourceCurrentRequiredHeapEffects.node (fun _ => True) first semantic costs
            (by intro _ _ _; trivial) (available _ List.mem_cons_self)
          obtain ⟨kept, returned⟩ := ih rest effects.2.1 effects.2.2.1
            (fun child member => effects.1.available child (available child (List.mem_cons_of_mem _ member)))
            (fun child member => closed child (List.mem_cons_of_mem _ member)) firstResult.1 tailInputs
          refine ⟨kept, ?_⟩
          intro index child selected
          cases index with
          | zero =>
              cases Option.some.inj selected
              simpa only [Nat.add_zero] using firstResult.2
          | succ index =>
              simpa only [Nat.add_assoc, Nat.add_comm 1 index] using returned index child selected
end Generic

open SourceSynthesisTypeSyntax (Library)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceCurrentAllocatedSharedEditGraph (SharedState advanceHeap)
open SourceRecursiveIntersectionKernel (Extension)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Ready" => SourceSynthesisNativeTypeSharedState.Ready
variable [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- Actual Required work retains shared readiness and full recursive fields at assigned slots. -/
theorem requireAll (lib : Library) (literal : String → Symbol) (assigned : Nat → Prop)
    {fuel readFuel : Nat} {paths : List (List Int)} {entries : List (Int × Needed)}
    {values results : List (Value Symbol Guard)} {before : SharedState width} {heap : State Symbol Guard}
    (actual : SourceEqualityRequiredExecution.requireAll fuel readFuel paths values before.checked.native.machine.heap =
      .done results heap)
    (compiled : SourceEqualityNeeded.build paths = .node entries)
    (ready : Ready lib before) (available : Values before.checked.native.machine.heap values)
    (closed : ClosedValues values)
    (typed : ∀ index value, values[index]? = some value → ¬ assigned index → Annotated (Origin lib) value)
    (fields : ∀ index value, values[index]? = some value → assigned index → ValueFields (Origin lib) literal value)
    (only : ∀ (index : Nat) children, SourceEqualityNeededMap.lookup (index : Int) entries = some (.node children) →
      assigned index → AnnotationOnly children) :
    Ready lib (advanceHeap before heap) ∧
      Extension before.checked.native.machine (advanceHeap before heap).checked.native.machine ∧
      Values heap results ∧ ClosedValues results ∧ results.length = values.length ∧
      ∀ index value, results[index]? = some value →
        (assigned index → ValueFields (Origin lib) literal value) ∧ (¬ assigned index → Annotated (Origin lib) value) := by
  have graph := (SourceEqualityRequiredExecution.requireAll_execution_iff paths values
    before.checked.native.machine.heap results heap).mpr ⟨fuel, readFuel, actual⟩
  simp only [compiled] at graph
  obtain ⟨_, returned⟩ := mixed_children (Origin lib) literal assigned graph ready.checked.semantic ready.costs
    available closed ready.checked.stored.constructors
    (fun index value found => by
      simpa only [Slot, Nat.zero_add] using And.intro (fields index value found) (typed index value found)) only
  have physical := SourceSynthesisNativeTypeRequired.requireAll lib assigned actual compiled ready available closed
    typed (fun index value found selected => (fields index value found selected).fields) only
  refine ⟨physical.1, physical.2.1, physical.2.2.1, physical.2.2.2.1, physical.2.2.2.2.1, ?_⟩
  intro index value found
  simpa only [Slot, Nat.zero_add] using returned index value found

end MicroCFTA.SourceSynthesisNativeTypeHereditaryRequired
