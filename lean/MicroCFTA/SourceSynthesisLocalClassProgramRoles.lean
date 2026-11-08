import MicroCFTA.SourceSynthesisSelectedRequiredProgramRoles
import MicroCFTA.SourceSynthesisClassPassProgramRoles
import MicroCFTA.SourceSynthesisActualSelectedProgramFootprints
import MicroCFTA.SourceCurrentParentOperationInvariants

/-!
# Program slots through actual local class reduction

The literal scan either erases every slot or returns selected records.
Required starts at that returned state. Class editing starts at the Required
return. Actual source guards and precheck receipts supply all path exclusions.
The proof derives intermediate physical facts and the intermediate slot.
These laws require a successful local return. Completion, failure-prefix
roles, all-reached roles, Type progress, and whole-driver bounds remain open.
-/
namespace MicroCFTA.SourceSynthesisLocalClassProgramRoles
open EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityClassOrder (Record)
open SourceEqualityNeeded (Needed)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisProgramBuildRolesGeneric (ProgramValue)
open SourceCurrentNativeOperationHeap (Good)
open SourceCurrentLowerOperationInvariants (Effect)
open SourceCurrentMemoMergeEffects (Stored)
open SourceCurrentAllocatedNativeEffects (physical)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
variable {width : Nat} {literal : String → Symbol}

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

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

private theorem classes_roles {g s r e p h m c n budget records values before fourth memo results after saved current}
    (actual : SourceCurrentAllocatedLocalWorker.classes g s r e p h m c n budget records values before fourth memo =
      .done results after saved current)
    (good : Good (width := width) before) (stored : Stored before.native.machine.heap memo)
    (available : Values before.native.machine.heap values) (index : Nat) {source result : Node}
    (input : values[index]? = some source) (output : results[index]? = some result)
    (role : ProgramValue literal source)
    (recordFootprints : ∀ {kept scanned scannedFourth},
      SourceCurrentAllocatedRecordScanWorker.scan g s p h n budget values records before fourth =
        .done (none, kept) scanned scannedFourth →
      ∀ record ∈ kept, SourceEqualityClassOrder.Coherent record ∧
        ∀ childIndex, childIndex ≠ 0 → SourceCurrentClassPositionalFootprints.Unselected record index childIndex)
    (annotationOnly : ∀ {kept scanned scannedFourth entries childEntries},
      SourceCurrentAllocatedRecordScanWorker.scan g s p h n budget values records before fourth =
        .done (none, kept) scanned scannedFourth →
      SourceEqualityNeeded.build (SourceEqualitySelectedRequired.paths (kept.map Record.paths)) = .node entries →
      SourceEqualityNeededMap.lookup (index : Int) entries = some (.node childEntries) →
      ∀ childIndex : Nat, childIndex ≠ 0 → SourceEqualityNeededMap.lookup (childIndex : Int) childEntries = none) :
    ProgramValue literal result := by
  cases scanCall : SourceCurrentAllocatedRecordScanWorker.scan g s p h n budget values records before fourth with
  | failed =>
      simp only [SourceCurrentAllocatedLocalWorker.classes, SourceCurrentAllocatedLocalWorker.scan,
        scanCall, SourceCurrentAllocatedLocalWorker.Outcome.bind] at actual
      cases actual
  | done selected checked scanned =>
      have later := actual
      simp only [SourceCurrentAllocatedLocalWorker.classes, SourceCurrentAllocatedLocalWorker.scan,
        scanCall, SourceCurrentAllocatedLocalWorker.Outcome.bind] at later
      cases selected with
      | mk stopped kept =>
          cases stopped with
          | some paths =>
              simp only at later
              cases later
              have member : result ∈ values.map (fun _ => (Value.empty : Node)) := List.mem_of_getElem? output
              obtain ⟨original, _included, same⟩ := List.mem_map.mp member
              cases same
              exact .empty
          | none =>
              simp only at later
              have projected : SourceCurrentAllocatedScanWorker.scan g s p h n budget values
                  (records.map Record.paths) before fourth =
                  .done (none, kept.map Record.paths) checked scanned := by
                rw [← SourceCurrentAllocatedRecordScanWorker.scan_mapPaths, scanCall]
                rfl
              have effect := SourceCurrentParentOperationInvariants.scan projected good available
              have scanAvailable : Values checked.native.machine.heap values :=
                fun value member => effect.keeps.available value (available value member)
              have footprints := recordFootprints scanCall
              obtain ⟨prepared, preparedBefore, next, warm, requiredDone, passDone⟩ := local_bind_done _ _ later
              cases requiredCall : SourceEqualityRequiredExecution.requireAll r h
                  (SourceEqualitySelectedRequired.paths (kept.map Record.paths)) values checked.native.machine.heap with
              | pending | unresolved | exhausted =>
                  simp only [SourceCurrentAllocatedLocalWorker.required, requiredCall] at requiredDone
                  cases requiredDone
              | done preparedValues preparedHeap =>
                  simp only [SourceCurrentAllocatedLocalWorker.required, requiredCall] at requiredDone
                  cases requiredDone
                  cases passCall : SourceCurrentAllocatedClassWorker.pass e p h m c n kept prepared
                      (SourceCurrentConjunctionClassScan.advanceHeap checked preparedHeap) memo with
                  | failed =>
                      simp only [SourceCurrentAllocatedLocalWorker.pass, passCall] at passDone
                      cases passDone
                  | done final finalChecked finalMemo =>
                      simp only [SourceCurrentAllocatedLocalWorker.pass, passCall] at passDone
                      cases passDone
                      have graph := (SourceEqualityRequiredExecution.requireAll_execution_iff _ _ _ _ _).mpr
                        ⟨r, h, requiredCall⟩
                      cases built : SourceEqualityNeeded.build
                          (SourceEqualitySelectedRequired.paths (kept.map Record.paths)) with
                      | node entries =>
                          simp only [built] at graph
                          have bound : index < prepared.length :=
                            graph.length ▸ (List.getElem?_eq_some_iff.mp input).choose
                          let narrowed : Node := prepared[index]
                          have narrowedInput : prepared[index]? = some narrowed :=
                            List.getElem?_eq_some_iff.mpr ⟨bound, rfl⟩
                          have narrowedRole := SourceSynthesisSelectedRequiredProgramRoles.requireAll_roles
                            requiredCall built effect.good.semantic effect.good.costs scanAvailable
                            index input narrowedInput role (fun _ found => annotationOnly scanCall built found)
                          obtain ⟨keeps, semantic, costs, fields, known⟩ := SourceCurrentRequiredHeapEffects.children
                            (SourceCurrentConjunctionEquality.FieldAvailable checked.operations)
                            graph effect.good.semantic effect.good.costs effect.good.fields scanAvailable
                          have physicalEffects : SourceCurrentConjunctionRowsAllocation.Effects
                              (physical checked) ⟨preparedHeap, checked.operations⟩ :=
                            ⟨keeps, ⟨semantic, costs, effect.good.operations, fields⟩,
                              SourceEqualityConstraintMemoAllocation.grows_refl _⟩
                          have preparedGood := effect.good.advance _ physicalEffects
                          exact SourceSynthesisClassPassProgramRoles.pass_roles passCall preparedGood
                            (stored.grows (effect.keeps.trans keeps)) known
                            (fun record member => (footprints record member).1) index
                            (fun record member => (footprints record member).2) narrowedInput output narrowedRole

open SourceSynthesisFirstOrderConstruction (Expression application ofType)
open SourceCurrentAllocatedPrecheck (Receipt)
variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
variable {solver : SourceGuards.Entailment FullSyntax.Formula}
variable {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
variable {guard : Guard} {loaded : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula}
variable {inherited own : SourceEqualityConstraintAllocation.Value} {initial : Checked width}
variable {records : List Record}

/-- An actual application local return retains either Program slot from source entry facts. -/
theorem application_classes_roles (types function argument : Expression)
    (sourceName : String) (sourceChildren : List Expression)
    (occurrence : application types function argument = .node [.mk sourceName guard sourceChildren])
    (receipt : Receipt formulas solver inventory guard loaded inherited initial own (.classes records))
    {g s r e p h m c n budget values fourth memo results after saved current}
    (actual : SourceCurrentAllocatedLocalWorker.classes g s r e p h m c n budget records values
      (SourceCurrentAllocatedPrecheck.state initial loaded inherited) fourth memo = .done results after saved current)
    (good : Good initial) (stored : Stored initial.native.machine.heap memo)
    (available : Values initial.native.machine.heap values) (index : Nat) (programSlot : index = 2 ∨ index = 3)
    {source result : Node} (input : values[index]? = some source) (output : results[index]? = some result)
    (role : ProgramValue literal source) : ProgramValue literal result := by
  have entryGood : Good (SourceCurrentAllocatedPrecheck.state initial loaded inherited) :=
    good.advance _ receipt.effects
  apply classes_roles actual entryGood stored available index input output role
  · intro kept scanned scannedFourth scanCall record member
    exact SourceSynthesisActualSelectedProgramFootprints.application_footprint types function argument
      sourceName sourceChildren occurrence receipt scanCall member index programSlot
  · intro kept scanned scannedFourth entries childEntries scanCall built found
    exact SourceSynthesisActualSelectedProgramFootprints.application_annotation_only types function argument
      sourceName sourceChildren occurrence receipt scanCall built index programSlot found

/-- An actual filter local return retains its candidate Program slot from source entry facts. -/
theorem filter_classes_roles (candidates goal : Expression)
    (sourceName : String) (sourceChildren : List Expression)
    (occurrence : ofType candidates goal = .node [.mk sourceName guard sourceChildren])
    (receipt : Receipt formulas solver inventory guard loaded inherited initial own (.classes records))
    {g s r e p h m c n budget values fourth memo results after saved current}
    (actual : SourceCurrentAllocatedLocalWorker.classes g s r e p h m c n budget records values
      (SourceCurrentAllocatedPrecheck.state initial loaded inherited) fourth memo = .done results after saved current)
    (good : Good initial) (stored : Stored initial.native.machine.heap memo)
    (available : Values initial.native.machine.heap values)
    {source result : Node} (input : values[1]? = some source) (output : results[1]? = some result)
    (role : ProgramValue literal source) : ProgramValue literal result := by
  have entryGood : Good (SourceCurrentAllocatedPrecheck.state initial loaded inherited) :=
    good.advance _ receipt.effects
  apply classes_roles actual entryGood stored available 1 input output role
  · intro kept scanned scannedFourth scanCall record member
    exact SourceSynthesisActualSelectedProgramFootprints.filter_footprint candidates goal
      sourceName sourceChildren occurrence receipt scanCall member
  · intro kept scanned scannedFourth entries childEntries scanCall built found
    exact SourceSynthesisActualSelectedProgramFootprints.filter_annotation_only candidates goal
      sourceName sourceChildren occurrence receipt scanCall built found

end MicroCFTA.SourceSynthesisLocalClassProgramRoles
