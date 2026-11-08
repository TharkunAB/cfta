import MicroCFTA.SourceCurrentHereditaryProgramRequired
import MicroCFTA.SourceSynthesisSelectedRequiredProgramRoles
import MicroCFTA.SourceSynthesisActualSelectedProgramFootprints

/-!
# Joint Program and Type-field facts through actual Required calls

Source positions assign each operand to a Type or a Program. Program guards
need no Type annotation. Actual selected requirements visit only their first
field. The ordered graph retains the conditional Mu store through every
sibling. Source precheck and scan receipts derive the required footprints.
These laws concern completed calls and genuine initial operand certificates.
They do not establish completion or all reached operand classifications.
-/
namespace MicroCFTA.SourceSynthesisJointProgramRequired
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityNeeded (Needed)
open SourceEqualityRequiredGraph
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisProgramBuildRolesGeneric (ProgramValue)
open SourceSynthesisTypePathRoles (AnnotationFields)
open SourceCurrentHereditaryConstruction (MuStored)
open SourceCurrentHereditaryProgramRequired (AnnotationOnly)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

section Generic
variable {Symbol : Type} {literal : String → Symbol}
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- One annotation-only Program request retains its strict role, Type fields, and Mu store. -/
theorem node (valid : Guard → Prop) {entries : List (Int × Needed)}
    {source result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : RequireNode (.node entries) source before result after)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Available before source) (closed : source.free = []) (stored : MuStored valid before)
    (role : ProgramValue literal source) (fields : AnnotationFields valid source) (only : AnnotationOnly entries) :
    MuStored valid after ∧ ProgramValue literal result ∧ AnnotationFields valid result := by
  obtain ⟨kept, returned⟩ := SourceCurrentHereditaryProgramRequired.node valid actual semantic costs
    available closed stored fields only
  exact ⟨kept, SourceSynthesisRequiredProgramRoles.required_roles actual semantic costs available role only, returned⟩

private def Slot (valid : Guard → Prop) (assigned : Nat → Prop) (index : Nat) (value : Value Symbol Guard) : Prop :=
  (assigned index → AnnotationFields valid value) ∧ (¬ assigned index → Annotated valid value)

private theorem mixed_children (valid : Guard → Prop) (assigned : Nat → Prop)
    {entries : List (Int × Needed)} {offset : Nat} {values results : List (Value Symbol Guard)}
    {before after : State Symbol Guard} (actual : RequireChildren entries offset values before results after)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Values before values) (closed : ClosedValues values) (stored : MuStored valid before)
    (inputs : ∀ index value, values[index]? = some value → Slot valid assigned (offset + index) value)
    (only : ∀ (index : Nat) children, SourceEqualityNeededMap.lookup (index : Int) entries = some (.node children) →
      assigned index → AnnotationOnly children) :
    MuStored valid after ∧ ∀ index value, results[index]? = some value → Slot valid assigned (offset + index) value := by
  classical
  induction values generalizing offset before results after with
  | nil =>
      cases actual
      refine ⟨stored, ?_⟩
      intro index value found
      simp only [List.getElem?_nil] at found
      cases found
  | cons value values ih =>
      have headInput : Slot valid assigned offset value := by
        simpa only [Nat.add_zero] using inputs 0 value rfl
      have tailInputs : ∀ index child, values[index]? = some child → Slot valid assigned (offset + 1 + index) child := by
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
              MuStored valid middle ∧ Slot valid assigned offset result := by
            intro needed result middle call selected
            cases needed with
            | node children =>
                by_cases program : assigned offset
                · obtain ⟨kept, returned⟩ := SourceCurrentHereditaryProgramRequired.node valid call semantic costs
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

/-- The literal mixed forest retains its selected Program operand and derives the final store. -/
theorem requireAll (valid : Guard → Prop) (assigned : Nat → Prop)
    {fuel readFuel : Nat} {paths : List (List Int)} {entries : List (Int × Needed)}
    {values results : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (actual : SourceEqualityRequiredExecution.requireAll fuel readFuel paths values before = .done results after)
    (compiled : SourceEqualityNeeded.build paths = .node entries)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Values before values) (closed : ClosedValues values) (stored : MuStored valid before)
    (typed : ∀ index value, values[index]? = some value → ¬ assigned index → Annotated valid value)
    (fields : ∀ index value, values[index]? = some value → assigned index → AnnotationFields valid value)
    (only : ∀ (index : Nat) children, SourceEqualityNeededMap.lookup (index : Int) entries = some (.node children) →
      assigned index → AnnotationOnly children)
    (index : Nat) (program : assigned index) {source : Value Symbol Guard}
    (input : values[index]? = some source) (role : ProgramValue literal source) :
    ∃ result, results[index]? = some result ∧ MuStored valid after ∧
      ProgramValue literal result ∧ AnnotationFields valid result := by
  have graph := (SourceEqualityRequiredExecution.requireAll_execution_iff paths values before results after).mpr
    ⟨fuel, readFuel, actual⟩
  simp only [compiled] at graph
  obtain ⟨kept, returned⟩ := mixed_children valid assigned graph semantic costs available closed stored
    (fun position value found => by
      simpa only [Slot, Nat.zero_add] using And.intro (fields position value found) (typed position value found)) only
  have bound : index < results.length := by
    rw [graph.length]
    exact (List.getElem?_eq_some_iff.mp input).choose
  let result := results[index]'bound
  have output : results[index]? = some result := List.getElem?_eq_some_iff.mpr ⟨bound, rfl⟩
  have outputFields : AnnotationFields valid result := by
    exact (returned index result output).1 (by simpa only [Nat.zero_add] using program)
  exact ⟨result, output, kept,
    SourceSynthesisSelectedRequiredProgramRoles.requireAll_roles actual compiled semantic costs available
      index input output role (fun children found => only index children found program), outputFields⟩
end Generic

section SelectedSource
open EqualityNormalize SourceEqualityClassOrder
open SourceSynthesisFirstOrderConstruction (Expression application ofType)
open SourceCurrentAllocatedPrecheck (Receipt)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
variable {width : Nat} {literal : String → Symbol}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
variable {solver : SourceGuards.Entailment FullSyntax.Formula}
variable {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
variable {guard : Guard} {loaded : Allocated} {inherited own : EqValue} {before scanned : Checked width}
variable {records kept : List Record} {g s p h n budget : Nat} {values : List Node}
variable {fourth savedFourth : SourceCurrentEmptinessMemo.Memo} {outcome : Option Class}
variable {fuel readFuel : Nat} {results : List Node} {finish : State Symbol Guard}

/-- Actual application selection supplies every Program footprint and retains the selected joint facts. -/
theorem application_requireAll (valid : Guard → Prop) (types function argument : Expression)
    (sourceName : String) (sourceChildren : List Expression)
    (occurrence : application types function argument = .node [.mk sourceName guard sourceChildren])
    (receipt : Receipt formulas solver inventory guard loaded inherited before own (.classes records))
    (scan : SourceCurrentAllocatedRecordScanWorker.scan g s p h n budget values records
      (SourceCurrentAllocatedPrecheck.state before loaded inherited) fourth =
        .done (outcome, kept) scanned savedFourth)
    (actual : SourceEqualityRequiredExecution.requireAll fuel readFuel
      (SourceEqualitySelectedRequired.paths (kept.map Record.paths)) values scanned.native.machine.heap = .done results finish)
    (semantic : SemanticReady scanned.native.machine.heap) (costs : CostHeap scanned.native.machine.heap)
    (available : Values scanned.native.machine.heap values) (closed : ClosedValues values)
    (stored : MuStored valid scanned.native.machine.heap)
    (typed : ∀ index value, values[index]? = some value → ¬ (index = 2 ∨ index = 3) → Annotated valid value)
    (fields : ∀ index value, values[index]? = some value → (index = 2 ∨ index = 3) → AnnotationFields valid value)
    (index : Nat) (programSlot : index = 2 ∨ index = 3) {source : Node}
    (input : values[index]? = some source) (role : ProgramValue literal source) :
    ∃ result, results[index]? = some result ∧ MuStored valid finish ∧
      ProgramValue literal result ∧ AnnotationFields valid result := by
  cases compiled : SourceEqualityNeeded.build (SourceEqualitySelectedRequired.paths (kept.map Record.paths)) with
  | node entries =>
      refine requireAll valid (fun position => position = 2 ∨ position = 3) actual compiled
        semantic costs available closed stored typed fields ?_ index programSlot input role
      intro position children found assigned
      exact SourceSynthesisActualSelectedProgramFootprints.application_annotation_only types function argument
        sourceName sourceChildren occurrence receipt scan compiled position assigned found

/-- Actual filter selection supplies every Program footprint and retains the selected joint facts. -/
theorem filter_requireAll (valid : Guard → Prop) (candidates goal : Expression)
    (sourceName : String) (sourceChildren : List Expression)
    (occurrence : ofType candidates goal = .node [.mk sourceName guard sourceChildren])
    (receipt : Receipt formulas solver inventory guard loaded inherited before own (.classes records))
    (scan : SourceCurrentAllocatedRecordScanWorker.scan g s p h n budget values records
      (SourceCurrentAllocatedPrecheck.state before loaded inherited) fourth =
        .done (outcome, kept) scanned savedFourth)
    (actual : SourceEqualityRequiredExecution.requireAll fuel readFuel
      (SourceEqualitySelectedRequired.paths (kept.map Record.paths)) values scanned.native.machine.heap = .done results finish)
    (semantic : SemanticReady scanned.native.machine.heap) (costs : CostHeap scanned.native.machine.heap)
    (available : Values scanned.native.machine.heap values) (closed : ClosedValues values)
    (stored : MuStored valid scanned.native.machine.heap)
    (typed : ∀ index value, values[index]? = some value → index ≠ 1 → Annotated valid value)
    (fields : ∀ index value, values[index]? = some value → index = 1 → AnnotationFields valid value)
    {source : Node} (input : values[1]? = some source) (role : ProgramValue literal source) :
    ∃ result, results[1]? = some result ∧ MuStored valid finish ∧
      ProgramValue literal result ∧ AnnotationFields valid result := by
  cases compiled : SourceEqualityNeeded.build (SourceEqualitySelectedRequired.paths (kept.map Record.paths)) with
  | node entries =>
      refine requireAll valid (fun position => position = 1) actual compiled semantic costs available closed stored
        typed fields ?_ 1 rfl input role
      intro position children found assigned
      subst position
      exact SourceSynthesisActualSelectedProgramFootprints.filter_annotation_only candidates goal
        sourceName sourceChildren occurrence receipt scan compiled found
end SelectedSource

end MicroCFTA.SourceSynthesisJointProgramRequired
