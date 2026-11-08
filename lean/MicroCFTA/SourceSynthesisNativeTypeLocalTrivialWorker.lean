import MicroCFTA.SourceSynthesisNativeTypeLocalPrefix
import MicroCFTA.SourceCurrentAllocatedLocalWorker
import MicroCFTA.SourceCurrentHereditaryTypeRouteConstructors
import MicroCFTA.SourceSynthesisTypePathRoles
import MicroCFTA.SourceEqualityEmptyPropagation

/-!
# Type facts through the two trivial local branches

An actual precheck receipt determines each literal worker return. Both
branches retain the returned equality operations, fourth memo, Merge memo,
and historical targets. Empty propagation preserves every Type route and
every supplied mixed slot classification.

These laws require successful precheck receipts. They do not prove precheck
completion, failed-return facts, all reached classifications, or a global
bound. The classes branch is proved in NativeTypeLocalWorker.
-/
namespace MicroCFTA.SourceSynthesisNativeTypeLocalTrivialWorker
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceSynthesisTypeSyntax (Library)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceSynthesisTypePathRoles (AnnotationFields)
open SourceCurrentHereditaryTypePaths (ForestPath)
open SourceCurrentHereditaryTypeRouteConstructors (ForestRoutes)
open SourceCurrentAllocatedPrecheck (Receipt)
open SourceRecursiveIntersectionKernel (Extension)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Shared" => SourceCurrentAllocatedSharedTargetState.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Ready" => SourceSynthesisNativeTypeSharedState.Ready
local notation "GuardHeap" => SourceCurrentConstrainedCapGuardHeap.Heap
local notation "prefixState" => SourceCurrentAllocatedPrecheck.state
local notation "advance" => SourceCurrentAllocatedSharedTargetState.advance
local notation "erase" => EqualityLeafProjectionRuntimeEmpty.erase

private theorem erased_routes (valid : Guard → Prop) (values : List Node) :
    ∀ path, ForestPath valid path (erase values) := by
  have typed : ∀ value ∈ erase values, Annotated valid value := by
    intro value member
    obtain ⟨original, included, rfl⟩ := List.mem_map.mp member
    exact .empty
  intro path
  cases path with
  | nil => exact typed
  | cons index path =>
      intro value found
      exact .annotated path value (typed value (SourceEqualityProjectionGraph.select_member found))

private theorem erased_slots (valid : Guard → Prop) (values : List Node) (assigned : Nat → Prop) :
    ∀ index value, (erase values)[index]? = some value →
      (assigned index → AnnotationFields valid value) ∧ (¬ assigned index → Annotated valid value) := by
  intro index value found
  have member : value ∈ erase values := List.mem_of_getElem? found
  obtain ⟨original, included, rfl⟩ := List.mem_map.mp member
  exact ⟨fun _ => .empty, fun _ => .empty⟩

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width : Nat}

/-- The unchanged branch retains every entry fact at its literal returned state. -/
theorem unchanged (lib : Library) (g s r e p h m c n budget : Nat)
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
    {original : Guard} {loaded : Allocated} {inherited own : EqValue}
    {values : List Node} {before : Shared width} (fourth : Fourth)
    (receipt : Receipt formulas solver inventory original loaded inherited before.checked own .unchanged)
    (ready : Ready lib before) (available : Values before.checked.native.machine.heap values)
    (closed : ClosedValues values) (guards : GuardHeap (Origin lib) before.checked.native.machine.heap) :
    SourceCurrentAllocatedLocalWorker.reduce g s r e p h m c n budget loaded inherited
        values before.checked fourth before.memo =
      .done values (prefixState before.checked loaded inherited) fourth before.memo ∧
      Ready lib (advance before (prefixState before.checked loaded inherited)) ∧
      Extension before.checked.native.machine (prefixState before.checked loaded inherited).native.machine ∧
      Values (prefixState before.checked loaded inherited).native.machine.heap values ∧ ClosedValues values ∧
      GuardHeap (Origin lib) (prefixState before.checked loaded inherited).native.machine.heap ∧
      ForestRoutes (Origin lib) values values ∧
      ∀ assigned : Nat → Prop,
        (∀ index value, values[index]? = some value →
          (assigned index → AnnotationFields (Origin lib) value) ∧
          (¬ assigned index → Annotated (Origin lib) value)) →
        ∀ index value, values[index]? = some value →
          (assigned index → AnnotationFields (Origin lib) value) ∧
          (¬ assigned index → Annotated (Origin lib) value) := by
  obtain ⟨next, extension⟩ := SourceSynthesisNativeTypeLocalPrefix.precheck lib receipt ready
  refine ⟨SourceCurrentAllocatedLocalWorker.reduce_unchanged g s r e p h m c n budget
    loaded inherited values before.checked fourth before.memo receipt.actual,
    next, extension, available, closed, guards, ?_, ?_⟩
  · exact fun _ route => route
  · exact fun _ slots => slots

/-- The contradictory branch erases slots and retains all historical shared facts. -/
theorem emptyChildren (lib : Library) (g s r e p h m c n budget : Nat)
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
    {original : Guard} {loaded : Allocated} {inherited own : EqValue}
    {values : List Node} {before : Shared width} (fourth : Fourth)
    (receipt : Receipt formulas solver inventory original loaded inherited before.checked own .emptyChildren)
    (ready : Ready lib before) (guards : GuardHeap (Origin lib) before.checked.native.machine.heap) :
    SourceCurrentAllocatedLocalWorker.reduce g s r e p h m c n budget loaded inherited
        values before.checked fourth before.memo =
      .done (erase values) (prefixState before.checked loaded inherited) fourth before.memo ∧
      Ready lib (advance before (prefixState before.checked loaded inherited)) ∧
      Extension before.checked.native.machine (prefixState before.checked loaded inherited).native.machine ∧
      Values (prefixState before.checked loaded inherited).native.machine.heap (erase values) ∧
      ClosedValues (erase values) ∧
      GuardHeap (Origin lib) (prefixState before.checked loaded inherited).native.machine.heap ∧
      ForestRoutes (Origin lib) values (erase values) ∧
      ∀ assigned : Nat → Prop, ∀ index value, (erase values)[index]? = some value →
        (assigned index → AnnotationFields (Origin lib) value) ∧
        (¬ assigned index → Annotated (Origin lib) value) := by
  obtain ⟨next, extension⟩ := SourceSynthesisNativeTypeLocalPrefix.precheck lib receipt ready
  obtain ⟨available, closed⟩ := SourceEqualityEmptyPropagation.erased_scope
    (prefixState before.checked loaded inherited).native.machine.heap values
  refine ⟨SourceCurrentAllocatedLocalWorker.reduce_emptyChildren g s r e p h m c n budget
    loaded inherited values before.checked fourth before.memo receipt.actual,
    next, extension, available, closed, guards, ?_, ?_⟩
  · exact fun path _ => erased_routes (Origin lib) values path
  · exact erased_slots (Origin lib) values

end MicroCFTA.SourceSynthesisNativeTypeLocalTrivialWorker
