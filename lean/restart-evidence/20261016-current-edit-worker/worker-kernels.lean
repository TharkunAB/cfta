import MicroCFTA.SourceCurrentAllocatedSharedEditWorker

namespace MicroCFTA.CurrentAllocatedSharedEditWorkerIntegration
open InternedConstructorTemplates SourceEqualityEdits
open SourceCurrentAllocatedSharedEditGraph (SharedState advanceHeap)
open SourceCurrentAllocatedSharedEditWorker
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Record" => SourceEqualityClassOrder.Record
local notation "Path" => EqualityNormalize.Path
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
theorem child_list_root_callback_is_not_executed
    (recur : Edits Path → Value Symbol Guard → SharedState width → Outcome width (Value Symbol Guard))
    (path : Path) (values : List (Value Symbol Guard)) (before : SharedState width) :
    editList recur (.editAt path) values before = .done values before := rfl

theorem zero_edit_bound_stops_before_empty_inspection
    (record : Record) (originals : List (Value Symbol Guard)) (before : SharedState width) :
    edit record originals 0 0 0 0 0 0 (.editBelow []) .empty before =
      .failed (.exhausted .worker) before ∧
    edit record originals 1 0 0 0 0 0 (.editBelow []) .empty before = .done .empty before := ⟨rfl, rfl⟩

theorem below_edit_at_bare_reference_keeps_unresolved_name
    (record : Record) (originals : List (Value Symbol Guard)) (name : InternedBinderProtocol.Reference)
    (before : SharedState width) :
    edit record originals 1 0 0 0 0 0 (.editBelow []) (.reference name) before =
      .failed (.unresolved name) before := rfl

theorem compiled_root_edit_skips_all_bounds_and_open_values
    (record : Record) (originals values : List (Value Symbol Guard)) (path : Path)
    (before : SharedState width) :
    editAll record originals 0 0 0 0 0 0 [([], path)] values before = .done values before := rfl

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
theorem negative_edit_key_does_not_select_an_existing_child
    (recur : Edits Path → Value Symbol Guard → SharedState width → Outcome width (Value Symbol Guard))
    (path : Path) (name : InternedBinderProtocol.Reference) (before : SharedState width) :
    children recur [(-1, .editAt path)] 0 [.reference name] before = .done [.reference name] before := rfl

theorem selected_child_failure_skips_open_sibling_and_retains_native_control
    (record : Record) (originals : List (Value Symbol Guard)) (path : Path)
    (name : InternedBinderProtocol.Reference) (input target : Value Symbol Guard) (before : SharedState width)
    (present : before.targets path = some target) :
    children (edit record originals 1 0 0 0 0 0) [(1, .editAt path)] 0 [.reference name, input] before =
      .failed (.leaf (.native (.yielded (.code (SourceRecursiveIntersectionCode.requestNode
        IntersectionEmptyDomain.emptyDomain target input)) before.checked))) before := by
  simp [children, SourceEqualityNeededMap.lookup, edit, leaf,
    SourceCurrentAllocatedSharedTargetWorker.leaf, SourceCurrentAllocatedSharedTargetWorker.force,
    SourceCurrentAllocatedSharedTargetWorker.Outcome.bind, present,
    SourceCurrentAllocatedSharedTargetWorker.step, SourceEqualityNativeDemand.execute,
    SourceEqualityNativeDemand.Outcome.state, lift,
    SourceCurrentAllocatedSharedTargetState.advance, Outcome.bind]

omit [DecidableEq Symbol] in
theorem head_failure_keeps_reached_heap_and_all_other_tables
    (h : Nat) (input : Value Symbol Guard) (before : SharedState width)
    (key : InternedBinderProtocol.NodeKey) (heap : InternedConstructorTemplates.State Symbol Guard)
    (pending : SourceEqualityRequiredWorker.head h input before.checked.native.machine.heap = .pending key heap) :
    head h input before = .failed (.pending key) (advanceHeap before heap) ∧
    (advanceHeap before heap).checked.operations = before.checked.operations ∧
    (advanceHeap before heap).checked.native.nodes = before.checked.native.nodes ∧
    (advanceHeap before heap).targets = before.targets ∧
    (advanceHeap before heap).memo = before.memo := by
  exact ⟨by simp only [head, pending], rfl, rfl, rfl, rfl⟩

omit [DecidableEq Symbol] in
theorem raw_row_rebuild_retains_original_guard_without_equality_allocation
    (recur : Edits Path → Value Symbol Guard → SharedState width → Outcome width (Value Symbol Guard))
    (entries : List (Int × Edits Path)) (entry : Cache.Interned (EdgeKey Symbol Guard)) (before : SharedState width) :
    let built := run (makeEdge entry.key.symbol entry.key.constraint []) before.checked.native.machine.heap
    rows recur entries [.mk entry []] before = .done [built.1] (advanceHeap before built.2) ∧
    (advanceHeap before built.2).checked.operations = before.checked.operations ∧
    (advanceHeap before built.2).checked.native.edges = before.checked.native.edges ∧
    (advanceHeap before built.2).checked.native.machine.domains = before.checked.native.machine.domains ∧
    (advanceHeap before built.2).targets = before.targets ∧
    (advanceHeap before built.2).memo = before.memo := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem failed_leaf_is_not_replaced_by_its_empty_input
    (record : Record) (originals : List (Value Symbol Guard)) (path : Path) (before : SharedState width)
    (fault : SourceCurrentAllocatedSharedTargetWorker.Fault width) (after : SharedState width)
    (failed : SourceCurrentAllocatedSharedTargetWorker.leaf 0 0 0 0 0 record originals path .empty before =
      .failed fault after) :
    edit record originals 1 0 0 0 0 0 (.editAt path) .empty before = .failed (.leaf fault) after := by
  simp only [edit, leaf, failed, lift]

end MicroCFTA.CurrentAllocatedSharedEditWorkerIntegration
