import MicroCFTA.SourceSynthesisLocalClassProgramRoles

/-!
# Program slots through the literal local precheck

The same actual precheck receipt selects unchanged children, erased children,
or the checked class continuation. Each source endpoint covers all branches.
The independent length law needs only a literal successful return.
These laws do not prove completion, failure-prefix roles, all-reached roles,
Type progress, or a whole-driver resource bound.
-/
namespace MicroCFTA.SourceSynthesisLocalReduceProgramRoles
open EqualityNormalize InternedConstructorTemplates
open InternedNestedProvenance (Values)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisProgramBuildRolesGeneric (ProgramValue)
open SourceCurrentNativeOperationHeap (Good)
open SourceCurrentMemoMergeEffects (Stored)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Shared" => SourceCurrentAllocatedSharedTargetState.State
local notation "Record" => SourceEqualityClassOrder.Record
variable {width : Nat} {literal : String → Symbol}

private theorem class_bind_done (first : SourceCurrentAllocatedClassWorker.Outcome width)
    (next : List Node → Checked width → Memo → SourceCurrentAllocatedClassWorker.Outcome width)
    {results after saved} (actual : first.bind next = .done results after saved) :
    ∃ values middle memo, first = .done values middle memo ∧ next values middle memo = .done results after saved := by
  cases first with
  | done values middle memo => exact ⟨values, middle, memo, rfl, actual⟩
  | failed => cases actual

private theorem local_bind_done {A B : Type}
    (first : SourceCurrentAllocatedLocalWorker.Outcome A width)
    (next : A → Checked width → Fourth → Memo → SourceCurrentAllocatedLocalWorker.Outcome B width)
    {output : B} {after : Checked width} {fourth : Fourth} {saved : Memo}
    (actual : first.bind next = .done output after fourth saved) :
    ∃ value middle current memo, first = .done value middle current memo ∧
      next value middle current memo = .done output after fourth saved := by
  cases first with
  | done value middle current memo => exact ⟨value, middle, current, memo, rfl, actual⟩
  | failed => cases actual

private theorem propagate_length (values : List Node) :
    (EqualityLeafProjectionRuntimeEmpty.propagate values).length = values.length := by
  unfold EqualityLeafProjectionRuntimeEmpty.propagate
  split
  · exact List.length_map _
  · rfl

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem class_length {e p h m c n record values memo results saved} {before after : Checked width}
    (actual : SourceCurrentAllocatedClassWorker.runClass e p h m c n record values before memo =
      .done results after saved) : results.length = values.length := by
  cases observed : SourceCurrentAllocatedSharedEditWorker.editList
      (SourceCurrentAllocatedSharedEditWorker.edit record values e p h m c n)
      (SourceCurrentAllocatedClassEditPlan.compiled record) values
      (SourceCurrentAllocatedSharedTargetState.initial before memo) with
  | failed =>
      simp only [SourceCurrentAllocatedClassWorker.runClass, observed] at actual
      cases actual
  | done outputs shared =>
      simp only [SourceCurrentAllocatedClassWorker.runClass, observed] at actual
      cases actual
      cases built : SourceCurrentAllocatedClassEditPlan.compiled record with
      | editAt target =>
          simp only [SourceCurrentAllocatedSharedEditWorker.editList, built] at observed
          cases observed
          rfl
      | editBelow entries =>
          exact SourceCurrentActualEditRowOrigins.children_length _
            (by simpa only [SourceCurrentAllocatedSharedEditWorker.editList, built] using observed)

private theorem fold_length {e p h m c n records values memo results saved} {before after : Checked width}
    (actual : SourceCurrentAllocatedClassWorker.fold e p h m c n records values before memo =
      .done results after saved) : results.length = values.length := by
  induction records generalizing values before memo results after saved with
  | nil => cases actual; rfl
  | cons record records ih =>
      obtain ⟨middle, checked, current, tail, head⟩ := class_bind_done _ _ actual
      exact (class_length head).trans (ih tail)

private theorem pass_length {e p h m c n records values memo results saved} {before after : Checked width}
    (actual : SourceCurrentAllocatedClassWorker.pass e p h m c n records values before memo =
      .done results after saved) : results.length = values.length := by
  obtain ⟨middle, checked, current, first, last⟩ := class_bind_done _ _ actual
  cases last
  exact (propagate_length middle).trans (fold_length first)

omit [DecidableEq Symbol] in
private theorem required_length {r h paths values fourth memo results saved current} {before after : Checked width}
    (actual : SourceCurrentAllocatedLocalWorker.required r h paths values before fourth memo =
      .done results after saved current) : results.length = values.length := by
  cases observed : SourceEqualityRequiredExecution.requireAll r h paths values before.native.machine.heap with
  | pending | unresolved | exhausted =>
      simp only [SourceCurrentAllocatedLocalWorker.required, observed] at actual
      cases actual
  | done output heap =>
      simp only [SourceCurrentAllocatedLocalWorker.required, observed] at actual
      cases actual
      have graph := (SourceEqualityRequiredExecution.requireAll_execution_iff _ _ _ _ _).mpr ⟨r, h, observed⟩
      cases built : SourceEqualityNeeded.build paths with
      | node entries =>
          simp only [built] at graph
          exact graph.length

private theorem local_pass_length {e p h m c n records values fourth memo results saved current} {before after : Checked width}
    (actual : SourceCurrentAllocatedLocalWorker.pass e p h m c n records values before fourth memo =
      .done results after saved current) : results.length = values.length := by
  cases observed : SourceCurrentAllocatedClassWorker.pass e p h m c n records values before memo with
  | failed =>
      simp only [SourceCurrentAllocatedLocalWorker.pass, observed] at actual
      cases actual
  | done output checked completed =>
      simp only [SourceCurrentAllocatedLocalWorker.pass, observed] at actual
      cases actual
      exact pass_length observed

variable [DecidableEq Node]

private theorem classes_length {g s r e p h m c n budget records values fourth memo results saved current} {before after : Checked width}
    (actual : SourceCurrentAllocatedLocalWorker.classes g s r e p h m c n budget records values before fourth memo =
      .done results after saved current) : results.length = values.length := by
  obtain ⟨selected, middle, completed, warm, first, later⟩ := local_bind_done _ _ actual
  cases stopped : selected.1 with
  | some paths =>
      simp only [stopped] at later
      cases later
      exact List.length_map _
  | none =>
      simp only [stopped] at later
      obtain ⟨prepared, checked, next, memo, required, passed⟩ := local_bind_done _ _ later
      exact (local_pass_length passed).trans (required_length required)

/-- Every literal successful local reduction retains the complete child-list length. -/
theorem reduce_length {g s r e p h m c n budget loaded inherited values fourth memo results saved current} {before after : Checked width}
    (actual : SourceCurrentAllocatedLocalWorker.reduce g s r e p h m c n budget loaded inherited values
      (before : Checked width) fourth memo = .done results after saved current) :
    results.length = values.length := by
  cases observed : (SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard inherited before.operations).1 with
  | error message =>
      simp only [SourceCurrentAllocatedLocalWorker.reduce, observed] at actual
      cases actual
  | ok branch =>
      cases branch with
      | unchanged =>
          simp only [SourceCurrentAllocatedLocalWorker.reduce, observed] at actual
          cases actual
          rfl
      | emptyChildren =>
          simp only [SourceCurrentAllocatedLocalWorker.reduce, observed] at actual
          cases actual
          exact List.length_map _
      | classes records =>
          exact classes_length (by simpa only [SourceCurrentAllocatedLocalWorker.reduce, observed] using actual)

open SourceSynthesisFirstOrderConstruction (Expression application ofType)
open SourceCurrentAllocatedPrecheck (Receipt)
variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
variable {solver : SourceGuards.Entailment FullSyntax.Formula}
variable {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
variable {guard : Guard} {loaded : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula}
variable {inherited own : SourceEqualityConstraintAllocation.Value} {before : Checked width}
variable {branch : SourceEqualityPrecheck.Branch}

/-- Every successful source application reduction retains either Program child role. -/
theorem application_reduce_roles (types function argument : Expression)
    (sourceName : String) (sourceChildren : List Expression)
    (occurrence : application types function argument = .node [.mk sourceName guard sourceChildren])
    (receipt : Receipt formulas solver inventory guard loaded inherited before own branch)
    {g s r e p h m c n budget values fourth memo results after saved current}
    (actual : SourceCurrentAllocatedLocalWorker.reduce g s r e p h m c n budget loaded inherited values
      before fourth memo = .done results after saved current)
    (good : Good before) (stored : Stored before.native.machine.heap memo)
    (available : Values before.native.machine.heap values) (index : Nat) (programSlot : index = 2 ∨ index = 3)
    {source result : Node} (input : values[index]? = some source) (output : results[index]? = some result)
    (role : ProgramValue literal source) : ProgramValue literal result := by
  cases branch with
  | unchanged =>
      simp only [SourceCurrentAllocatedLocalWorker.reduce, receipt.actual] at actual
      cases actual
      cases Option.some.inj (input.symm.trans output)
      exact role
  | emptyChildren =>
      simp only [SourceCurrentAllocatedLocalWorker.reduce, receipt.actual] at actual
      cases actual
      have member : result ∈ values.map (fun _ => (Value.empty : Node)) := List.mem_of_getElem? output
      obtain ⟨original, _included, same⟩ := List.mem_map.mp member
      cases same
      exact .empty
  | classes records =>
      have live := actual
      simp only [SourceCurrentAllocatedLocalWorker.reduce, receipt.actual] at live
      exact SourceSynthesisLocalClassProgramRoles.application_classes_roles types function argument
        sourceName sourceChildren occurrence receipt live good stored available index programSlot input output role

/-- Every successful source filter reduction retains its candidate Program child role. -/
theorem filter_reduce_roles (candidates goal : Expression)
    (sourceName : String) (sourceChildren : List Expression)
    (occurrence : ofType candidates goal = .node [.mk sourceName guard sourceChildren])
    (receipt : Receipt formulas solver inventory guard loaded inherited before own branch)
    {g s r e p h m c n budget values fourth memo results after saved current}
    (actual : SourceCurrentAllocatedLocalWorker.reduce g s r e p h m c n budget loaded inherited values
      before fourth memo = .done results after saved current)
    (good : Good before) (stored : Stored before.native.machine.heap memo)
    (available : Values before.native.machine.heap values)
    {source result : Node} (input : values[1]? = some source) (output : results[1]? = some result)
    (role : ProgramValue literal source) : ProgramValue literal result := by
  cases branch with
  | unchanged =>
      simp only [SourceCurrentAllocatedLocalWorker.reduce, receipt.actual] at actual
      cases actual
      cases Option.some.inj (input.symm.trans output)
      exact role
  | emptyChildren =>
      simp only [SourceCurrentAllocatedLocalWorker.reduce, receipt.actual] at actual
      cases actual
      have member : result ∈ values.map (fun _ => (Value.empty : Node)) := List.mem_of_getElem? output
      obtain ⟨original, _included, same⟩ := List.mem_map.mp member
      cases same
      exact .empty
  | classes records =>
      have live := actual
      simp only [SourceCurrentAllocatedLocalWorker.reduce, receipt.actual] at live
      exact SourceSynthesisLocalClassProgramRoles.filter_classes_roles candidates goal
        sourceName sourceChildren occurrence receipt live good stored available input output role

end MicroCFTA.SourceSynthesisLocalReduceProgramRoles
