import MicroCFTA.SourceSecondaryGateReplay
import MicroCFTA.SourceEqualityAnnotationHeap

/-!
# Physical edge annotations through actual secondary gate traces

Each actual stored unfolding copies resident constraints. Other gate steps
reuse existing edge records. Semantic replay effects derive the intermediate
availability needed by ordered sibling queries. The complete trace retains
every physical edge-annotation predicate without a final-heap premise.
-/
namespace MicroCFTA.SourceSecondaryGateHeap
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedFreshOrdinaryStatefulGateTrace EqualityNormalize
open SourceEqualityRequiredSemanticCache
open SourceEqualityAnnotationHeap (Heap)

private def NodeHeap (property : Guard → Prop) (value : Value Symbol Guard)
    (before after : State Symbol Guard) : Prop :=
  SemanticReady before → Available before value → Heap property before → Heap property after

private def ChildHeap (property : Guard → Prop) (values : List (Value Symbol Guard))
    (before after : State Symbol Guard) : Prop :=
  SemanticReady before → (∀ value ∈ values, Available before value) → Heap property before → Heap property after

private def EdgesHeap (property : Guard → Prop) (edges : List (EdgeValue Symbol Guard))
    (before after : State Symbol Guard) : Prop :=
  SemanticReady before → (∀ value ∈ edges.flatMap EdgeValue.children, Available before value) →
    Heap property before → Heap property after

private theorem node_effects (property : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool)
    {path : Path} {value : Value Symbol Guard} {before after : State Symbol Guard} {answer : Bool}
    (trace : NodeTrace unconstrained path value before answer after) : NodeHeap property value before after := by
  induction trace using NodeTrace.rec
      (motive_2 := fun values _ _ before _ after _ => ChildHeap property values before after)
      (motive_3 := fun _ _ edges before _ after _ => EdgesHeap property edges before after) with
  | empty | reference | union | finite | endpoint | constrained | closed => intro _ _ heap; exact heap
  | branches slow trace ih => intro semantic available heap; exact ih semantic (fun value member => available.children value member) heap
  | unfold plain opened actual trace ih =>
      intro semantic available heap
      obtain ⟨result, middle, done, _, middleSemantic, resultAvailable, _⟩ :=
        SourceEqualityOpenOrdinaryHead.unfold_complete _ _ semantic available
      obtain ⟨sameValue, sameState⟩ := Outcome.done.inj (done.symm.trans actual)
      cases sameValue
      cases sameState
      apply ih middleSemantic resultAvailable
      have retained := InternedFreshOrdinaryStoredConstraintHeap.unfold_heap property _ _
        semantic.ready.semantic.1.normal.facts heap available
      simpa only [InternedFreshOrdinaryConstraintHeap.Heap, Heap, actual, Outcome.state] using retained
  | missing => intro _ _ heap; exact heap
  | present found trace ih => intro semantic available heap; exact ih semantic (available _ (List.mem_of_getElem? found)) heap
  | nil => intro _ _ heap; exact heap
  | stop head ih => intro semantic available heap; exact ih semantic (fun value member => available value (by simp [member])) heap
  | next head tail headIH tailIH =>
      intro semantic available heap
      have first := SourceSecondaryGateReplay.child_replay _ _ _ _ _ _ _ head semantic
        (fun value member => available value (by simp [member]))
      exact tailIH first.1
        (fun value member => first.2.1.available value (available value (by simp [member])))
        (headIH semantic (fun value member => available value (by simp [member])) heap)

/-- An actual node gate preserves every physical edge-annotation predicate in its returned heap. -/
theorem node_heap (property : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool)
    {path : Path} {value : Value Symbol Guard} {before after : State Symbol Guard} {answer : Bool}
    (trace : NodeTrace unconstrained path value before answer after)
    (semantic : SemanticReady before) (available : Available before value) (heap : Heap property before) :
    Heap property after :=
  node_effects property unconstrained trace semantic available heap

/-- A completed forest-path gate preserves the physical annotation heap. -/
theorem path_heap (property : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool)
    {values : List (Value Symbol Guard)} {path : Path} {before after : State Symbol Guard} {answer : Bool}
    (trace : PathTrace unconstrained values path before answer after)
    (semantic : SemanticReady before) (available : ∀ value ∈ values, Available before value) (heap : Heap property before) :
    Heap property after := by
  cases trace with
  | empty => exact heap
  | child trace =>
      cases trace with
      | missing => exact heap
      | present found trace => exact node_heap property unconstrained trace semantic (available _ (List.mem_of_getElem? found)) heap

/-- Ordered class gates retain every physical annotation while threading their actual returned states. -/
theorem class_heap (property : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool)
    {values : List (Value Symbol Guard)} {paths : Class} {before after : State Symbol Guard} {answer : Bool}
    (trace : ClassTrace unconstrained values paths before answer after)
    (semantic : SemanticReady before) (available : ∀ value ∈ values, Available before value) (heap : Heap property before) :
    Heap property after := by
  revert heap available semantic
  induction trace with
  | nil => intro _ _ heap; exact heap
  | stop head => intro semantic available heap; exact path_heap property unconstrained head semantic available heap
  | next head tail ih =>
      intro semantic available heap
      have first := SourceSecondaryGateReplay.path_replay _ _ _ _ _ _ head semantic available
      exact ih first.1 (fun value member => first.2.1.available value (available value member))
        (path_heap property unconstrained head semantic available heap)

end MicroCFTA.SourceSecondaryGateHeap
