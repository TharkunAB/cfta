import MicroCFTA.SourceSynthesisClassProgramRoles

/-!
# Program slots through the actual ordered class pass

The literal right fold executes its tail before its head class.
Every head uses the forest and physical state returned by that tail.
Source precheck and retained selection derive the per-record footprints.
Final Empty propagation either keeps the forest or erases every slot.
These laws require successful local returns. They do not prove completion,
failure-prefix roles, Type progress, or an all-reached traversal bound.
-/
namespace MicroCFTA.SourceSynthesisClassPassProgramRoles
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentClassPositionalFootprints (Unselected)
open SourceSynthesisProgramBuildRolesGeneric (ProgramValue)
open SourceSynthesisGeneralizeSyntax (Guard)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Good" => SourceCurrentNativeOperationHeap.Good
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Stored" => SourceCurrentMemoMergeEffects.Stored
variable {width : Nat} {literal : String → Symbol}

private theorem class_bind_done
    (first : SourceCurrentAllocatedClassWorker.Outcome width)
    (next : List Node → Checked width → Memo → SourceCurrentAllocatedClassWorker.Outcome width)
    {output : List Node} {after : Checked width} {saved : Memo}
    (actual : first.bind next = .done output after saved) :
    ∃ values middle current, first = .done values middle current ∧
      next values middle current = .done output after saved := by
  cases first with
  | done values middle current => exact ⟨values, middle, current, rfl, actual⟩
  | failed => cases actual

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Each actual head class preserves the Program role returned by its tail. -/
theorem fold_roles {e p h m s n records values memo results saved} {before after : Checked width}
    (actual : SourceCurrentAllocatedClassWorker.fold e p h m s n records values before memo =
      .done results after saved)
    (good : Good before) (stored : Stored before.native.machine.heap memo)
    (available : Values before.native.machine.heap values)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record) (index : Nat)
    (footprints : ∀ record ∈ records, ∀ childIndex, childIndex ≠ 0 →
      Unselected record index childIndex)
    {source result : Node} (input : values[index]? = some source)
    (output : results[index]? = some result) (role : ProgramValue literal source) :
    ProgramValue literal result := by
  induction records generalizing values before memo results after saved source result with
  | nil =>
      simp only [SourceCurrentAllocatedClassWorker.fold] at actual
      cases actual
      cases Option.some.inj (input.symm.trans output)
      exact role
  | cons record records ih =>
      obtain ⟨middle, checked, current, first, last⟩ := class_bind_done _ _
        (by simpa only [SourceCurrentAllocatedClassWorker.fold] using actual)
      have headFootprint := footprints record List.mem_cons_self
      obtain ⟨entries, shared, start, finish, original, built, sameState, sameMemo, found,
        earlier, later, dispatch⟩ := SourceCurrentClassPositionalFootprints.class_dispatch last
          (coherent record List.mem_cons_self) index 1 (headFootprint 1 (by decide)) output
      have tailRole := ih first good stored available
        (fun record member => coherent record (List.mem_cons_of_mem _ member))
        (fun record member => footprints record (List.mem_cons_of_mem _ member)) input found role
      obtain ⟨effect, retained, known⟩ :=
        SourceCurrentLowerOperationInvariants.class_fold first good stored available
      exact SourceSynthesisClassProgramRoles.run_class_roles last effect.good retained known
        (coherent record List.mem_cons_self) index headFootprint found output tailRole

/-- Final propagation retains a Program slot or replaces it with literal Empty. -/
theorem pass_roles {e p h m s n records values memo results saved} {before after : Checked width}
    (actual : SourceCurrentAllocatedClassWorker.pass e p h m s n records values before memo =
      .done results after saved)
    (good : Good before) (stored : Stored before.native.machine.heap memo)
    (available : Values before.native.machine.heap values)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record) (index : Nat)
    (footprints : ∀ record ∈ records, ∀ childIndex, childIndex ≠ 0 →
      Unselected record index childIndex)
    {source result : Node} (input : values[index]? = some source)
    (output : results[index]? = some result) (role : ProgramValue literal source) :
    ProgramValue literal result := by
  obtain ⟨middle, checked, current, first, last⟩ := class_bind_done _ _
    (by simpa only [SourceCurrentAllocatedClassWorker.pass] using actual)
  cases last
  by_cases erased : middle.any (fun value => value.referenceOf == .empty) = true
  · have member : result ∈ middle.map (fun _ => (Value.empty : Node)) := by
      simpa only [EqualityLeafProjectionRuntimeEmpty.propagate, erased, ite_true,
        EqualityLeafProjectionRuntimeEmpty.erase] using List.mem_of_getElem? output
    obtain ⟨original, included, same⟩ := List.mem_map.mp member
    cases same
    exact .empty
  · have same : EqualityLeafProjectionRuntimeEmpty.propagate middle = middle := by
      simp [EqualityLeafProjectionRuntimeEmpty.propagate, erased]
    exact fold_roles first good stored available coherent index footprints input
      (by simpa only [same] using output) role

open EqualityNormalize
open SourceSynthesisFirstOrderConstruction (Expression application ofType)

section SelectedSource
variable [DecidableEq Node]
variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
variable {solver : SourceGuards.Entailment FullSyntax.Formula}
variable {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
variable {guard : Guard} {loaded : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula}
variable {inherited own : SourceEqualityConstraintAllocation.Value} {initial scanned : Checked width}
variable {records kept : List SourceEqualityClassOrder.Record} {budget : Nat} {values : List Node}
variable {fourth savedFourth : SourceCurrentEmptinessMemo.Memo}
variable {outcome : Option Class} {selected : Constraints}
variable {scan : SourceCurrentConjunctionClassScan.Scan budget SourceMemoGate.unconstrained
  (SourceEndpointReachability.reaches SourceMemoGate.unconstrained) values
  (records.map SourceEqualityClassOrder.Record.paths)
  (SourceCurrentAllocatedPrecheck.state initial loaded inherited) fourth outcome selected scanned savedFourth}

/-- Actual source application selection supplies every footprint for its Program slots. -/
theorem selected_application_pass_roles (types function argument : Expression)
    (name : String) (children : List Expression)
    (occurrence : application types function argument = .node [.mk name guard children])
    (receipt : SourceCurrentAllocatedPrecheck.Receipt formulas solver inventory guard loaded inherited initial own
      (.classes records))
    (retained : SourceCurrentConjunctionSelectedRecords.Retained scan records kept)
    {e p h m s n prepared memo results saved} {before after : Checked width}
    (actual : SourceCurrentAllocatedClassWorker.pass e p h m s n kept prepared before memo =
      .done results after saved)
    (good : Good before) (stored : Stored before.native.machine.heap memo)
    (available : Values before.native.machine.heap prepared) (index : Nat)
    (programSlot : index = 2 ∨ index = 3)
    {source result : Node} (input : prepared[index]? = some source)
    (output : results[index]? = some result) (role : ProgramValue literal source) :
    ProgramValue literal result := by
  have footprints := fun record member =>
    SourceSynthesisClassProgramRoles.selected_application_footprint types function argument name children
      occurrence receipt retained (record := record) member index programSlot
  exact pass_roles actual good stored available
    (fun record member => (footprints record member).1) index
    (fun record member => (footprints record member).2) input output role

/-- Actual source filter selection supplies every footprint for its candidate Program slot. -/
theorem selected_filter_pass_roles (candidates goal : Expression)
    (name : String) (children : List Expression)
    (occurrence : ofType candidates goal = .node [.mk name guard children])
    (receipt : SourceCurrentAllocatedPrecheck.Receipt formulas solver inventory guard loaded inherited initial own
      (.classes records))
    (retained : SourceCurrentConjunctionSelectedRecords.Retained scan records kept)
    {e p h m s n prepared memo results saved} {before after : Checked width}
    (actual : SourceCurrentAllocatedClassWorker.pass e p h m s n kept prepared before memo =
      .done results after saved)
    (good : Good before) (stored : Stored before.native.machine.heap memo)
    (available : Values before.native.machine.heap prepared)
    {source result : Node} (input : prepared[1]? = some source)
    (output : results[1]? = some result) (role : ProgramValue literal source) :
    ProgramValue literal result := by
  have footprints := fun record member =>
    SourceSynthesisClassProgramRoles.selected_filter_footprint candidates goal name children
      occurrence receipt retained (record := record) member
  exact pass_roles actual good stored available
    (fun record member => (footprints record member).1) 1
    (fun record member => (footprints record member).2) input output role
end SelectedSource

end MicroCFTA.SourceSynthesisClassPassProgramRoles
