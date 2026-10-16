import MicroCFTA.SourceCurrentAllocatedSharedEditWorkerCompletion
import MicroCFTA.SourceCurrentAllocatedSharedEditComplete

namespace MicroCFTA.AllocatedEditCompletionKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityEdits SourceEqualityEditLeafPaths SourceCurrentEditDomains
open SourceEqualitySharedEditEffects (Allowed)
open SourceEqualityProjectionPathDomain (ForestClosed)
open SourceCurrentAllocatedSharedEditGraph
open SourceCurrentAllocatedSharedEditWorker
open SourceCurrentAllocatedSharedEditWorkerCompletion
open SourceCurrentAllocatedNativeInventoryState (Inventory)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A list-root leaf ignores every worker stage and retains the complete shared state. -/
theorem root_leaf_has_zero_bound (record : SourceEqualityClassOrder.Record)
    (originals values : List (Value Symbol Guard)) (target : EqualityNormalize.Path) (before : SharedState width) :
    editList (edit record originals 0 0 0 0 0 0) (.editAt target) values before = .done values before ∧
      StableRun (fun e p h m s n => editList (edit record originals e p h m s n) (.editAt target) values before) values before :=
  ⟨rfl, list_complete .leaf⟩

/-- Two selected leaves use the literal state returned by the earlier child. -/
theorem selected_children_keep_order
    {record : SourceEqualityClassOrder.Record} {originals : List (Value Symbol Guard)}
    {entries : List (Int × Edits EqualityNormalize.Path)} {firstPath secondPath : EqualityNormalize.Path}
    {first second firstResult secondResult : Value Symbol Guard} {before middle after : SharedState width}
    (selectedFirst : SourceEqualityNeededMap.lookup (0 : Int) entries = some (.editAt firstPath))
    (selectedSecond : SourceEqualityNeededMap.lookup (1 : Int) entries = some (.editAt secondPath))
    (firstLeaf : SourceCurrentAllocatedSharedTargetLeaf.Leaf record originals firstPath first before firstResult middle)
    (secondLeaf : SourceCurrentAllocatedSharedTargetLeaf.Leaf record originals secondPath second middle secondResult after) :
    StableRun (fun e p h m s n => children (edit record originals e p h m s n) entries 0 [first, second] before)
      [firstResult, secondResult] after :=
  children_complete (.selected 0 selectedFirst (.leaf firstLeaf) (.selected 1 selectedSecond (.leaf secondLeaf) .nil))

/-- An unrelated open child is retained without creating a recursive edit premise for that child. -/
theorem unselected_open_child_is_retained
    {record : SourceEqualityClassOrder.Record} {originals : List (Value Symbol Guard)}
    {entries : List (Int × Edits EqualityNormalize.Path)} {path : EqualityNormalize.Path}
    (name : InternedBinderProtocol.Reference) {input result : Value Symbol Guard} {before after : SharedState width}
    (unselected : SourceEqualityNeededMap.lookup (0 : Int) entries = none)
    (selected : SourceEqualityNeededMap.lookup (1 : Int) entries = some (.editAt path))
    (actual : SourceCurrentAllocatedSharedTargetLeaf.Leaf record originals path input before result after) :
    StableRun (fun e p h m s n => children (edit record originals e p h m s n) entries 0 [.reference name, input] before)
      [.reference name, result] after :=
  children_complete (.unselected 0 unselected (.selected 1 selected (.leaf actual) .nil))

/-- The row request uses the original full raw guard and retains operations and both shared tables. -/
theorem row_rebuild_uses_full_guard
    {record : SourceEqualityClassOrder.Record} {originals : List (Value Symbol Guard)}
    {entries : List (Int × Edits EqualityNormalize.Path)} {edge result : EdgeValue Symbol Guard}
    {values : List (Value Symbol Guard)} {before middle : SharedState width}
    {heap : InternedConstructorTemplates.State Symbol Guard}
    (childrenActual : EditChildren record originals entries 0 edge.children before values middle)
    (built : run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.checked.native.machine.heap = (result, heap)) :
    StableRun (fun e p h m s n => rows (edit record originals e p h m s n) entries [edge] before)
      [result] (advanceHeap middle heap) ∧
      (advanceHeap middle heap).checked.operations = middle.checked.operations ∧
      (advanceHeap middle heap).targets = middle.targets ∧ (advanceHeap middle heap).memo = middle.memo :=
  ⟨rows_complete (.cons childrenActual built .nil), rfl, rfl, rfl⟩

/-- Recursive row exposure precedes the actual below-edit at its returned heap. -/
theorem recursive_head_then_body
    {record : SourceEqualityClassOrder.Record} {originals : List (Value Symbol Guard)}
    {entries : List (Int × Edits EqualityNormalize.Path)}
    {original exposed result : Value Symbol Guard} {before after : SharedState width}
    {heap : InternedConstructorTemplates.State Symbol Guard}
    (recursive : SourceEqualityRequiredGraph.Recursive original)
    (headActual : SourceEqualityRequiredHead.Head original before.checked.native.machine.heap exposed heap)
    (bodyActual : EditNode record originals (.editBelow entries) exposed (advanceHeap before heap) result after) :
    StableRun (fun e p h m s n => edit record originals e p h m s n (.editBelow entries) original before) result after :=
  node_complete (.recursive recursive headActual bodyActual)

/-- Initial selected domains derive both the finite graph and its literal stable execution. -/
theorem initial_facts_construct_stable_list_and_same_receipt
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard))
    (base : InternedConstructorTemplates.State Symbol Guard) (known : Values base originals)
    (domains : ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) originals)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (inventory : Inventory) {edits values} {before : SharedState width}
    (ranges : SourceCurrentAllocatedSharedEditRanges.ListRanges record originals edits values before)
    (populated : Populated edits) (allowed : Allowed record edits)
    (ready : SourceCurrentAllocatedSharedTargetState.Ready formulas solver inventory record originals base before)
    (available : Values before.checked.native.machine.heap values)
    (safe : SourceCurrentAllocatedSharedEditEffects.ListSafe edits values)
    (memos : EndpointMemoGateTrace.Memos) (valid : EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos) :
    ∃ results after next final, ∃ actual : EditList record originals edits values before results after,
      StableRun (fun e p h m s n => editList (edit record originals e p h m s n) edits values before) results after ∧
      ListReads formulas solver base actual memos final ∧
      SourceCurrentAllocatedSharedEditEffects.ChildrenReceipt formulas solver next record originals base values before results after memos final := by
  obtain ⟨results, after, next, final, actual, reads, receipt⟩ :=
    SourceCurrentAllocatedSharedEditComplete.list_complete formulas solver record originals base known domains coherent active
      inventory ranges populated allowed ready available safe memos valid
  exact ⟨results, after, next, final, actual, list_complete actual, reads, receipt⟩

/-- The signed compiler and generic list worker share one graph-derived return and uniform bound. -/
theorem compiled_signed_edits_share_uniform_return
    {record : SourceEqualityClassOrder.Record} {originals : List (Value Symbol Guard)}
    {signed : List (Path × EqualityNormalize.Path)} {values results : List (Value Symbol Guard)}
    {before after : SharedState width}
    (actual : EditList record originals (build signed) values before results after) :
    ∃ bound, ∀ fuel, bound ≤ fuel →
      editAll record originals fuel fuel fuel fuel fuel fuel signed values before = .done results after ∧
      editList (edit record originals fuel fuel fuel fuel fuel fuel) (build signed) values before = .done results after := by
  obtain ⟨bound, done⟩ := editAll_uniform actual
  exact ⟨bound, fun fuel enough => ⟨done fuel enough, done fuel enough⟩⟩

#print axioms root_leaf_has_zero_bound
#print axioms selected_children_keep_order
#print axioms unselected_open_child_is_retained
#print axioms row_rebuild_uses_full_guard
#print axioms recursive_head_then_body
#print axioms initial_facts_construct_stable_list_and_same_receipt
#print axioms compiled_signed_edits_share_uniform_return
set_option pp.explicit true
#check @root_leaf_has_zero_bound
#check @selected_children_keep_order
#check @unselected_open_child_is_retained
#check @row_rebuild_uses_full_guard
#check @recursive_head_then_body
#check @initial_facts_construct_stable_list_and_same_receipt
#check @compiled_signed_edits_share_uniform_return
end MicroCFTA.AllocatedEditCompletionKernels
