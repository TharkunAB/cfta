import MicroCFTA.SourceSynthesisRequiredProgramRoles
import MicroCFTA.SourceSynthesisSelectedProgramFootprints

/-!
# Program slots through actual selected Required calls

The indexed child proof derives each selected sibling's returned heap facts.
An absent sibling is unchanged. Source precheck and retained-selection receipts
derive the annotation-only condition for application and filter Program slots.
These laws describe successful returns. They do not establish completion,
failure-prefix roles, inherited layouts, Type progress, or a whole-driver bound.
-/
namespace MicroCFTA.SourceSynthesisSelectedRequiredProgramRoles
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityNeeded (Needed)
open SourceEqualityRequiredGraph
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceSynthesisProgramBuildRolesGeneric (ProgramValue)
open SourceSynthesisGeneralizeSyntax (Guard)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

section Indexed
variable {Symbol : Type} {literal : String → Symbol}
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Actual ordered child calls preserve an annotation-only Program slot. -/
theorem children_roles {entries : List (Int × Needed)} {offset : Nat}
    {values results : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (actual : RequireChildren entries offset values before results after)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before values)
    (index : Nat) {source result : Value Symbol Guard}
    (input : values[index]? = some source) (output : results[index]? = some result)
    (role : ProgramValue literal source)
    (annotationOnly : ∀ childEntries,
      SourceEqualityNeededMap.lookup ((offset + index : Nat) : Int) entries = some (.node childEntries) →
      ∀ childIndex : Nat, childIndex ≠ 0 → SourceEqualityNeededMap.lookup (childIndex : Int) childEntries = none) :
    ProgramValue literal result := by
  induction index generalizing offset values results before after with
  | zero =>
      cases actual with
      | nil => cases input
      | unselected =>
          cases Option.some.inj input
          cases Option.some.inj output
          exact role
      | selected offset found first rest =>
          cases Option.some.inj input
          cases Option.some.inj output
          cases observed : SourceEqualityNeededMap.lookup (offset : Int) entries with
          | none => rw [observed] at found; cases found
          | some selectedNeeded =>
              have same := Option.some.inj (observed.symm.trans found)
              rw [← same] at first
              cases selectedNeeded with
              | node childEntries =>
                  exact SourceSynthesisRequiredProgramRoles.required_roles first semantic costs
                    (available _ List.mem_cons_self) role
                    (annotationOnly childEntries (by simpa using observed))
  | succ index ih =>
      cases actual with
      | nil => cases input
      | unselected offset absent rest =>
          have sameIndex : offset + 1 + index = offset + (index + 1) := by omega
          exact ih rest semantic costs
            (fun value member => available value (List.mem_cons_of_mem _ member)) input output
            (by simpa only [sameIndex] using annotationOnly)
      | selected offset found first rest =>
          have effects := SourceCurrentRequiredHeapEffects.node (fun _ => True) first semantic costs
            (by intro _ _ _; trivial) (available _ List.mem_cons_self)
          have sameIndex : offset + 1 + index = offset + (index + 1) := by omega
          exact ih rest effects.2.1 effects.2.2.1
            (fun value member => effects.1.available value (available value (List.mem_cons_of_mem _ member)))
            input output (by simpa only [sameIndex] using annotationOnly)

/-- The literal compiled requireAll preserves the indexed Program role. -/
theorem requireAll_roles {fuel readFuel : Nat} {paths : List (List Int)}
    {values results : List (Value Symbol Guard)} {before after : State Symbol Guard}
    {entries : List (Int × Needed)}
    (actual : SourceEqualityRequiredExecution.requireAll fuel readFuel paths values before = .done results after)
    (compiled : SourceEqualityNeeded.build paths = .node entries)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before values)
    (index : Nat) {source result : Value Symbol Guard}
    (input : values[index]? = some source) (output : results[index]? = some result)
    (role : ProgramValue literal source)
    (annotationOnly : ∀ childEntries,
      SourceEqualityNeededMap.lookup (index : Int) entries = some (.node childEntries) →
      ∀ childIndex : Nat, childIndex ≠ 0 → SourceEqualityNeededMap.lookup (childIndex : Int) childEntries = none) :
    ProgramValue literal result := by
  have graph := (SourceEqualityRequiredExecution.requireAll_execution_iff paths values before results after).mpr
    ⟨fuel, readFuel, actual⟩
  simp only [compiled] at graph
  exact children_roles graph semantic costs available index input output role
    (by simpa only [Nat.zero_add] using annotationOnly)
end Indexed

section SourceSelection
open EqualityNormalize SourceEqualityClassOrder
open SourceSynthesisFirstOrderConstruction (Expression application ofType)
open SourceCurrentAllocatedPrecheck (Receipt)
open SourceCurrentConjunctionClassScan (Scan)
open SourceCurrentConjunctionSelectedRecords (Retained)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "sourceGate" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches sourceGate
variable {width : Nat} {literal : String → Symbol}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
variable {solver : SourceGuards.Entailment FullSyntax.Formula}
variable {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
variable {loaded : Allocated} {inherited own : EqValue} {before scanned : Checked width}
variable {records kept : List Record} {budget : Nat} {values : List Node}
variable {fourth savedFourth : SourceCurrentEmptinessMemo.Memo}
variable {outcome : Option Class} {selected : Constraints}
variable {scan : Scan budget sourceGate reaches values (records.map Record.paths)
  (SourceCurrentAllocatedPrecheck.state before loaded inherited) fourth outcome selected scanned savedFourth}

/-- Actual selected application paths retain both Program slots through requireAll. -/
theorem application_requireAll_roles (types function argument : Expression)
    (sourceName : String) (guard : Guard) (sourceChildren : List Expression)
    (occurrence : application types function argument = .node [.mk sourceName guard sourceChildren])
    (receipt : Receipt formulas solver inventory guard loaded inherited before own (.classes records))
    (retained : Retained scan records kept) {fuel readFuel : Nat} {results : List Node} {after : State Symbol Guard}
    (actual : SourceEqualityRequiredExecution.requireAll fuel readFuel
      (SourceEqualitySelectedRequired.paths (kept.map Record.paths)) values scanned.native.machine.heap = .done results after)
    (semantic : SemanticReady scanned.native.machine.heap) (costs : CostHeap scanned.native.machine.heap)
    (available : Values scanned.native.machine.heap values)
    (index : Nat) (programSlot : index = 2 ∨ index = 3) {source result : Node}
    (input : values[index]? = some source) (output : results[index]? = some result)
    (role : ProgramValue literal source) : ProgramValue literal result := by
  cases compiled : SourceEqualityNeeded.build (SourceEqualitySelectedRequired.paths (kept.map Record.paths)) with
  | node entries =>
      apply requireAll_roles actual compiled semantic costs available index input output role
      intro childEntries found
      exact SourceSynthesisSelectedProgramFootprints.application_annotation_only types function argument
        sourceName guard sourceChildren occurrence receipt retained compiled index programSlot found

/-- Actual selected filter paths retain the candidate Program slot through requireAll. -/
theorem filter_requireAll_roles (candidates goal : Expression)
    (sourceName : String) (guard : Guard) (sourceChildren : List Expression)
    (occurrence : ofType candidates goal = .node [.mk sourceName guard sourceChildren])
    (receipt : Receipt formulas solver inventory guard loaded inherited before own (.classes records))
    (retained : Retained scan records kept) {fuel readFuel : Nat} {results : List Node} {after : State Symbol Guard}
    (actual : SourceEqualityRequiredExecution.requireAll fuel readFuel
      (SourceEqualitySelectedRequired.paths (kept.map Record.paths)) values scanned.native.machine.heap = .done results after)
    (semantic : SemanticReady scanned.native.machine.heap) (costs : CostHeap scanned.native.machine.heap)
    (available : Values scanned.native.machine.heap values) {source result : Node}
    (input : values[1]? = some source) (output : results[1]? = some result)
    (role : ProgramValue literal source) : ProgramValue literal result := by
  cases compiled : SourceEqualityNeeded.build (SourceEqualitySelectedRequired.paths (kept.map Record.paths)) with
  | node entries =>
      apply requireAll_roles actual compiled semantic costs available 1 input output role
      intro childEntries found
      exact SourceSynthesisSelectedProgramFootprints.filter_annotation_only candidates goal
        sourceName guard sourceChildren occurrence receipt retained compiled found
end SourceSelection

end MicroCFTA.SourceSynthesisSelectedRequiredProgramRoles
