import MicroCFTA.EndpointMemoGateClasses
import MicroCFTA.SourceCurrentSecondaryProjectionScoped
import MicroCFTA.SourceEqualityExposureCosts

/-!
# Projection support from actual false primary gates

A false primary trace supplies a current secondary certificate with the
same unfolding equations and returned heaps. This proof does not execute
another gate or add a memo call. The certificate supplies projection
support at the actual primary final heap. Other forest values can be open.

These results do not preserve support through requireAll or class edits.
-/
namespace MicroCFTA.SourceCurrentPrimaryProjectionSupport
open InternedConstructorTemplates InternedProbeProvenance EqualityNormalize
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentSecondaryProjectionSupport (Support)
open SourceCurrentSecondaryProjectionScoped (PathSupport)
local notation "GateReady" => InternedFreshOrdinaryMemoGateTrace.Ready
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

private theorem node_false_aux [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained reaches : Value Symbol Guard → Bool}
    {path : Path} {value : Value Symbol Guard} {before final : State Symbol Guard} {answer : Bool}
    (trace : EndpointStatefulGateTrace.NodeTrace unconstrained reaches path value before answer final) :
    answer = false → SourceCurrentSecondaryTrace.NodeTrace unconstrained path value before false final := by
  induction trace using EndpointStatefulGateTrace.NodeTrace.rec
      (motive_2 := fun values index path before answer final _ => answer = false →
        SourceCurrentSecondaryTrace.ChildTrace unconstrained values index path before false final)
      (motive_3 := fun index path edges before answer final _ => answer = false →
        SourceCurrentSecondaryTrace.EdgesTrace unconstrained index path edges before false final) with
  | empty => intro _; exact .empty
  | reference => intro impossible; cases impossible
  | union => intro impossible; cases impossible
  | finite fast => intro _; exact .finite fast
  | endpoint slow =>
      intro cleared
      have closed := (Bool.or_eq_false_iff.mp cleared).1
      simpa only [closed] using (SourceCurrentSecondaryTrace.NodeTrace.endpoint (unconstrained := unconstrained) slow)
  | branches slow trace ih => intro cleared; exact .branches slow (ih cleared)
  | constrained => intro impossible; cases impossible
  | closed plain closed => intro _; exact .closed plain closed
  | unfold plain opened actual trace ih => intro cleared; exact .unfold plain opened actual (ih cleared)
  | missing absent _ => exact .missing absent
  | present found trace ih cleared => exact .present found (ih cleared)
  | nil _ => exact .nil
  | stop _ _ impossible => cases impossible
  | next head tail headIH tailIH cleared => exact .next (headIH rfl) (tailIH cleared)

/-- A false primary node supplies a secondary certificate at exactly the same heaps. -/
theorem node_false [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained reaches : Value Symbol Guard → Bool}
    {path : Path} {value : Value Symbol Guard} {before final : State Symbol Guard}
    (trace : EndpointStatefulGateTrace.NodeTrace unconstrained reaches path value before false final) :
    SourceCurrentSecondaryTrace.NodeTrace unconstrained path value before false final := node_false_aux trace rfl

/-- A false primary path retains its selected slot and every actual unfolding. -/
theorem path_false [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained reaches : Value Symbol Guard → Bool}
    {values : List (Value Symbol Guard)} {path : Path} {before final : State Symbol Guard}
    (trace : EndpointStatefulGateTrace.PathTrace unconstrained reaches values path before false final) :
    SourceCurrentSecondaryTrace.PathTrace unconstrained values path before false final := by
  cases trace with
  | empty => exact .empty
  | child trace =>
      cases trace with
      | missing absent => exact .child (.missing absent)
      | present found trace => exact .child (.present found (node_false trace))

private theorem class_false_aux [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained reaches : Value Symbol Guard → Bool}
    {values : List (Value Symbol Guard)} {paths : Class} {before final : State Symbol Guard} {answer : Bool}
    (trace : EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths before answer final) :
    answer = false → SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths before false final := by
  induction trace with
  | nil => intro _; exact .nil
  | stop => intro impossible; cases impossible
  | next head tail ih => intro cleared; exact .next (path_false head) (ih cleared)

/-- A false primary class supplies ordered certificates with its exact intermediate heaps. -/
theorem class_false [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained reaches : Value Symbol Guard → Bool}
    {values : List (Value Symbol Guard)} {paths : Class} {before final : State Symbol Guard}
    (trace : EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths before false final) :
    SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths before false final := class_false_aux trace rfl

/-- The actual primary final heap anchors the original node's projection support. -/
theorem node_support [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained reaches : Value Symbol Guard → Bool}
    {path : Path} {value : Value Symbol Guard} {before final : State Symbol Guard}
    (trace : EndpointStatefulGateTrace.NodeTrace unconstrained reaches path value before false final)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before value) :
    SemanticReady final ∧ GateReady final ∧ Keeps before final ∧ Available final value ∧
      Support unconstrained final path value := by
  have anchored := SourceCurrentSecondaryProjectionAnchor.node_anchor unconstrained (node_false trace)
    semantic (SourceEqualityExposureCosts.gate_ready semantic costs) available
  exact ⟨anchored.1, anchored.2.1, anchored.2.2.1, anchored.2.2.2.1,
    Or.inr ⟨anchored.2.2.2.1, anchored.2.2.2.2⟩⟩

/-- A proper original path has signed operand support at the actual primary final heap. -/
theorem path_support [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained reaches : Value Symbol Guard → Bool}
    {values : List (Value Symbol Guard)} {path : Path} {before final : State Symbol Guard}
    (trace : EndpointStatefulGateTrace.PathTrace unconstrained reaches values path before false final)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before values)
    (nonroot : path ≠ []) :
    SemanticReady final ∧ GateReady final ∧ Keeps before final ∧ Values final values ∧
      PathSupport unconstrained final (path.map Int.ofNat) values := by
  have anchored := SourceCurrentSecondaryProjectionAnchor.path_anchor unconstrained (path_false trace)
    semantic (SourceEqualityExposureCosts.gate_ready semantic costs) available
  exact ⟨anchored.1, anchored.2.1, anchored.2.2.1, anchored.2.2.2.1,
    SourceCurrentSecondaryProjectionScoped.path_support_of_false anchored.2.2.2.2 nonroot anchored.2.2.2.1⟩

/-- Every proper original class path is supported at the returned primary heap. -/
theorem class_support [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained reaches : Value Symbol Guard → Bool}
    {values : List (Value Symbol Guard)} {paths : Class} {before final : State Symbol Guard}
    (trace : EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths before false final)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before values)
    (nonroot : ∀ path ∈ paths, path ≠ []) :
    SemanticReady final ∧ GateReady final ∧ Keeps before final ∧ Values final values ∧
      ∀ path ∈ paths, PathSupport unconstrained final (path.map Int.ofNat) values :=
  SourceCurrentSecondaryProjectionScoped.class_support unconstrained (class_false trace) semantic
    (SourceEqualityExposureCosts.gate_ready semantic costs) available nonroot

/-- Actual later head rows retain support for their exact selected child positions. -/
theorem head_selected_support [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained reaches : Value Symbol Guard → Bool}
    {index : Nat} {path : Path} {original exposed : Value Symbol Guard}
    {before final caller after : State Symbol Guard}
    (gate : EndpointStatefulGateTrace.NodeTrace unconstrained reaches (index :: path) original before false final)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before original)
    (callerSemantic : SemanticReady caller) (callerAvailable : Available caller original) (growth : Grows final caller)
    (actual : SourceEqualityRequiredHead.Head original caller exposed after) :
    ∀ edge ∈ InternedEdgeResidency.nodeEdges exposed, ∀ child, edge.children[index]? = some child →
      Support unconstrained final path child := by
  have anchored := SourceCurrentSecondaryProjectionAnchor.node_anchor unconstrained (node_false gate)
    semantic (SourceEqualityExposureCosts.gate_ready semantic costs) available
  exact SourceCurrentSecondaryProjectionSupport.head_selected_support anchored.2.2.2.2
    anchored.1 anchored.2.2.2.1 callerSemantic callerAvailable growth actual

end MicroCFTA.SourceCurrentPrimaryProjectionSupport
