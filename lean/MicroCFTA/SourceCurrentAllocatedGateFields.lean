import MicroCFTA.SourceCurrentConjunctionRowsAllocation
import MicroCFTA.SourceCurrentClassGateCompletion
import MicroCFTA.SourceCurrentOpenExposureFields
import MicroCFTA.SourceCurrentSecondaryProjectionScoped

/-!
# Loaded physical fields through gates and projections

Actual gates, reads, and path projections retain the same equality-operation
state. Their constructor effects copy existing physical fields. The input
fields include successful read-only loads, not only normalized classes.

Anchored support derives finite selected-path projection without closing
unrelated original children. Native intersection and seeded folds need a
separate allocation proof. No conjunction closure premise is used here.
The completed graph schedule has a separate GHC forcing boundary.
-/
namespace MicroCFTA.SourceCurrentAllocatedGateFields
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentConjunctionEquality (FieldAvailable Fields)
open SourceEqualityProjectionGraph
open SourceCurrentSecondaryProjectionSupport (Support)
open SourceCurrentSecondaryProjectionComplete (ForestSupport)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol Formula
local notation "GateReady" => InternedFreshOrdinaryMemoGateTrace.Ready

private theorem same_operations (before : Physical) (ready : Ready before)
    (after : State Symbol Guard) (keeps : Keeps before.heap after)
    (semantic : SemanticReady after) (costs : InternedFreshOrdinaryCostHeap.Heap after)
    (fields : Fields before.equality after) : Effects before ⟨after, before.equality⟩ :=
  ⟨keeps, ⟨semantic, costs, ready.valid, fields⟩,
    SourceEqualityConstraintMemoAllocation.grows_refl before.equality⟩

/-- The primary class gate retains every existing physical load in the same operation state. -/
theorem primary_class [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained reaches : Value Symbol Guard → Bool)
    {values : List (Value Symbol Guard)} {paths : EqualityNormalize.Class}
    {before : Physical} {answer : Bool} {heap : State Symbol Guard}
    (actual : EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths before.heap answer heap)
    (ready : Ready before) (available : Values before.heap values) :
    Effects before ⟨heap, before.equality⟩ ∧ Values heap values := by
  have checked := SourcePrimaryGateEffects.class_effects (FieldAvailable before.equality)
    unconstrained reaches actual ready.semantic ready.costs available ready.fields
  exact ⟨same_operations before ready heap checked.2.1 checked.1 checked.2.2.1 checked.2.2.2,
    fun value member => checked.2.1.available value (available value member)⟩

/-- The current secondary class gate retains complete loaded fields for open or closed inputs. -/
theorem secondary_class [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool)
    {values : List (Value Symbol Guard)} {paths : EqualityNormalize.Class}
    {before : Physical} {answer : Bool} {heap : State Symbol Guard}
    (actual : SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths before.heap answer heap)
    (ready : Ready before) (available : Values before.heap values) :
    Effects before ⟨heap, before.equality⟩ ∧ Values heap values := by
  have checked := SourceCurrentSecondaryEffects.class_effects (FieldAvailable before.equality)
    unconstrained actual ready.semantic ready.costs available ready.fields
  exact ⟨same_operations before ready heap checked.2.1 checked.1 checked.2.2.1 checked.2.2.2,
    fun value member => checked.2.1.available value (available value member)⟩

/-- Initial physical readiness derives a finite primary gate and retained loaded fields. -/
theorem primary_complete [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained reaches : Value Symbol Guard → Bool) (values : List (Value Symbol Guard))
    (paths : EqualityNormalize.Class) (before : Physical) (ready : Ready before)
    (available : Values before.heap values) :
    ∃ answer heap, EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths before.heap answer heap ∧
      Effects before ⟨heap, before.equality⟩ ∧ Values heap values := by
  obtain ⟨_, answer, heap, actual, _⟩ := SourceCurrentClassGateCompletion.primary_class_complete
    unconstrained reaches values paths before.heap ready.semantic ready.costs available
  exact ⟨answer, heap, actual, primary_class unconstrained reaches actual ready available⟩

/-- Initial physical readiness derives a finite current secondary gate and retained loaded fields. -/
theorem secondary_complete [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained reaches : Value Symbol Guard → Bool) (values : List (Value Symbol Guard))
    (paths : EqualityNormalize.Class) (before : Physical) (ready : Ready before)
    (available : Values before.heap values) :
    ∃ answer heap, SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths before.heap answer heap ∧
      Effects before ⟨heap, before.equality⟩ ∧ Values heap values := by
  obtain ⟨_, answer, heap, actual, _⟩ := SourceCurrentClassGateCompletion.secondary_class_complete
    unconstrained reaches values paths before.heap ready.semantic ready.costs available
  exact ⟨answer, heap, actual, secondary_class unconstrained actual ready available⟩

/-- A completed nodeEdges read copies loaded fields without changing the equality-operation state. -/
theorem read [DecidableEq (EdgeKey Symbol Guard)]
    {value : Value Symbol Guard} {before : Physical} {heap : State Symbol Guard}
    {edges : List (EdgeValue Symbol Guard)}
    (actual : SourceEqualityProjectionRead.Read value before.heap edges heap)
    (ready : Ready before) (available : Available before.heap value) :
    Effects before ⟨heap, before.equality⟩ ∧ Edges heap edges := by
  have checked := SourceEqualityProjectionCosts.read_effects actual ready.semantic ready.costs available
  have fields : Fields before.equality heap := by
    cases actual with
    | done fuel completed =>
        simpa only [Fields, completed, MergedSourceExposure.Result.state] using
          SourceCurrentOpenExposureFields.nodeEdges_heap (FieldAvailable before.equality) fuel value before.heap
            ready.semantic ready.fields available
  exact ⟨same_operations before ready heap checked.1 checked.2.1 checked.2.2.1 fields, checked.2.2.2⟩

/-- Actual ordinary-head reconstruction retains loaded fields even when its original value is open. -/
theorem head [DecidableEq (EdgeKey Symbol Guard)]
    {value result : Value Symbol Guard} {before : Physical} {heap : State Symbol Guard}
    (actual : SourceEqualityRequiredHead.Head value before.heap result heap)
    (ready : Ready before) (available : Available before.heap value) :
    Effects before ⟨heap, before.equality⟩ ∧ Available heap result := by
  have checked := SourceEqualityProjectionCosts.head_effects actual ready.semantic ready.costs available
  have fields : Fields before.equality heap := by
    cases actual with
    | read fuel edges middle exposed rebuilt =>
        have first := read (SourceEqualityProjectionRead.Read.done fuel exposed) ready available
        have final := SourceEqualityAnnotationHeap.run (FieldAvailable before.equality) _
          (SourceEqualityAnnotationHeap.makeNode (FieldAvailable before.equality) edges) middle first.1.ready.fields
        simpa only [Fields, rebuilt] using final
  exact ⟨same_operations before ready heap checked.1 checked.2.1 checked.2.2.1 fields, checked.2.2.2⟩

/-- Supported natural-path projection retains current loaded fields and derives its closed result. -/
theorem project [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    {path : EqualityNormalize.Path} {value result : Value Symbol Guard}
    {before : Physical} {heap : State Symbol Guard}
    (actual : Project (path.map Int.ofNat) value before.heap result heap)
    (ready : Ready before) (available : Available before.heap value) (growth : Grows anchor before.heap)
    (supported : Support unconstrained anchor path value) :
    Effects before ⟨heap, before.equality⟩ ∧ Available heap result ∧ result.free = [] := by
  have checked := SourceCurrentSecondaryProjectionComplete.node_verified unconstrained anchor anchorSemantic anchorReady
    actual ready.semantic available growth supported
  have fields := SourceCurrentSecondaryProjectionHeap.node_heap (FieldAvailable before.equality)
    unconstrained anchor anchorSemantic anchorReady actual ready.semantic available growth supported ready.fields
  have costs := SourceEqualityProjectionCosts.project_effects actual ready.semantic ready.costs available
  exact ⟨same_operations before ready heap checked.1 checked.2.1 costs.2.2.1 fields, checked.2.2⟩

/-- Supported forest projection keeps the same operation state and does not close unrelated children. -/
theorem forest [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    {path : EqualityNormalize.Path} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before : Physical} {heap : State Symbol Guard}
    (actual : Forest (path.map Int.ofNat) values before.heap result heap)
    (ready : Ready before) (available : Values before.heap values) (growth : Grows anchor before.heap)
    (supported : ForestSupport unconstrained anchor path values) :
    Effects before ⟨heap, before.equality⟩ ∧ Available heap result ∧ result.free = [] := by
  have checked := SourceCurrentSecondaryProjectionComplete.forest_verified unconstrained anchor anchorSemantic anchorReady
    actual ready.semantic available growth supported
  have fields := SourceCurrentSecondaryProjectionHeap.forest_heap (FieldAvailable before.equality)
    unconstrained anchor anchorSemantic anchorReady actual ready.semantic available growth supported ready.fields
  have costs := SourceEqualityProjectionCosts.forest_effects actual ready.semantic ready.costs available
  exact ⟨same_operations before ready heap checked.1 checked.2.1 costs.2.2.1 fields, checked.2.2⟩

/-- Anchored support derives a finite actual forest projection with all current physical loads retained. -/
theorem forest_complete [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    (path : EqualityNormalize.Path) (values : List (Value Symbol Guard)) (before : Physical)
    (ready : Ready before) (available : Values before.heap values) (growth : Grows anchor before.heap)
    (supported : ForestSupport unconstrained anchor path values) :
    ∃ result heap, Forest (path.map Int.ofNat) values before.heap result heap ∧
      Effects before ⟨heap, before.equality⟩ ∧ Available heap result ∧ result.free = [] := by
  obtain ⟨result, heap, actual, _⟩ := SourceCurrentSecondaryProjectionComplete.forest_complete
    unconstrained anchor anchorSemantic anchorReady path values before.heap ready.semantic available growth supported
  exact ⟨result, heap, actual, forest unconstrained anchor anchorSemantic anchorReady actual ready available growth supported⟩

/-- An actual false class derives finite projection at its returned anchor and keeps every loaded field. -/
theorem false_class_path_complete [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool)
    {paths : EqualityNormalize.Class} {values : List (Value Symbol Guard)}
    {before : Physical} {anchor : State Symbol Guard}
    (gate : SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths before.heap false anchor)
    (ready : Ready before) (available : Values before.heap values)
    (path : EqualityNormalize.Path) (member : path ∈ paths) (proper : path ≠ []) :
    ∃ result heap, Forest (path.map Int.ofNat) values anchor result heap ∧
      Effects before ⟨heap, before.equality⟩ ∧ Available heap result ∧ result.free = [] := by
  obtain ⟨anchorSemantic, anchorReady, _, anchorValues, _, certificates⟩ :=
    SourceCurrentSecondaryProjectionAnchor.class_anchor unconstrained gate ready.semantic
      (SourceCurrentClassGateCompletion.gate_ready ready.semantic ready.costs) available
  have first := secondary_class unconstrained gate ready available
  have supported := SourceCurrentSecondaryProjectionComplete.false_path_support
    (certificates path member) proper anchorValues
  obtain ⟨result, heap, actual, later, resident, closed⟩ := forest_complete unconstrained anchor
    anchorSemantic anchorReady path values ⟨anchor, before.equality⟩ first.1.ready anchorValues
      (grows_refl anchor) supported
  exact ⟨result, heap, actual, first.1.trans later, resident, closed⟩

end MicroCFTA.SourceCurrentAllocatedGateFields
