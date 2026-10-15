import MicroCFTA.InternedSourceClassSelection
import MicroCFTA.SourceEqualityRequiredSemanticCache

/-!
# Actual gate caches for closed source forests

Closed ordinary records have closed children. A closed Mu query stops before
unfolding. Thus complete gate traces on closed source forests return the
original constructor cache. This proves the required semantic-cache fields
after selection without identifying different ready-cache predicates.
-/
namespace MicroCFTA.SourceClosedGateCache
open InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open InternedFreshOrdinaryStatefulGateTrace

/-- Every complete gate query on a closed available node returns the original constructor cache. -/
theorem node_state [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {path value before answer after}
    (trace : NodeTrace unconstrained path value before answer after) :
    Facts before → Available before value → value.free = [] → after = before := by
  induction trace using NodeTrace.rec
      (motive_2 := fun values _ _ before _ after _ =>
        Facts before → Values before values → ClosedValues values → after = before)
      (motive_3 := fun _ _ edges before _ after _ =>
        Facts before → Edges before edges → ClosedEdges edges → after = before) with
  | empty | reference | union | finite | endpoint | constrained | closed => intros; rfl
  | branches slow trace ih =>
      intro facts available closed
      exact ih facts (InternedEdgeResidency.resident_edges _ facts.linked _ available.resident)
        (MergedColdReaderClosed.node_children_closed _ facts _ _ _ _ available closed)
  | unfold plain opened actual trace ih =>
      intro facts available closed
      simp only [closed, List.isEmpty_nil] at opened
      cases opened
  | missing absent => intros; rfl
  | present found trace ih =>
      rename_i facts available closed
      have member := List.mem_of_getElem? found
      exact ih facts (available _ member) (closed _ member)
  | nil => intros; rfl
  | stop head ih =>
      rename_i facts resident closed
      exact ih facts (facts.cached.edges _ _ (resident _ List.mem_cons_self)) (closed _ List.mem_cons_self)
  | next head tail headIH tailIH =>
      rename_i facts resident closed
      have same := headIH facts (facts.cached.edges _ _ (resident _ List.mem_cons_self)) (closed _ List.mem_cons_self)
      cases same
      exact tailIH facts (fun edge member => resident edge (List.mem_cons_of_mem _ member))
        (fun edge member => closed edge (List.mem_cons_of_mem _ member))

/-- Child lookup cannot cause constructor effects on a closed forest. -/
theorem child_state [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {values index path before answer after}
    (trace : ChildTrace unconstrained values index path before answer after)
    (facts : Facts before) (available : Values before values) (closed : ClosedValues values) : after = before := by
  cases trace with
  | missing absent => rfl
  | present found trace =>
      have member := List.mem_of_getElem? found
      exact node_state trace facts (available _ member) (closed _ member)

/-- Each complete path query retains the original cache on a closed forest. -/
theorem path_state [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {values path before answer after}
    (trace : PathTrace unconstrained values path before answer after)
    (facts : Facts before) (available : Values before values) (closed : ClosedValues values) : after = before := by
  cases trace with
  | empty => rfl
  | child trace => exact child_state trace facts available closed

/-- Ordered class short circuit retains the cache on a closed forest. -/
theorem class_state [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {values paths before answer after}
    (trace : ClassTrace unconstrained values paths before answer after) :
    Facts before → Values before values → ClosedValues values → after = before := by
  induction trace with
  | nil => intros; rfl
  | stop head => exact path_state head
  | next head tail ih =>
      intro facts available closed
      have same := path_state head facts available closed
      cases same
      exact ih facts available closed

/-- Actual ordered class selection returns the original constructor cache on closed inputs. -/
theorem selection_state [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {values classes before queries after}
    (trace : InternedSourceClassSelection.Trace unconstrained values classes before queries after) :
    Facts before → Values before values → ClosedValues values → after = before := by
  induction trace with
  | nil => intros; rfl
  | cons head tail ih =>
      intro facts available closed
      have same := class_state head facts available closed
      cases same
      exact ih facts available closed

/-- The actual retained selection cache derives every independent semantic-ready field. -/
theorem selection_semantic [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {values classes before queries after}
    (trace : InternedSourceClassSelection.Trace unconstrained values classes before queries after)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before)
    (available : Values before values) (closed : ClosedValues values) :
    SourceEqualityRequiredSemanticCache.SemanticReady after := by
  have same := selection_state trace semantic.ready.semantic.1.normal.facts available closed
  exact same ▸ semantic

end MicroCFTA.SourceClosedGateCache
