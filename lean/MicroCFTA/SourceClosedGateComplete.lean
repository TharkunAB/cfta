import MicroCFTA.SourceClosedGateMemoSelection

/-!
# Finite gate queries on closed available forests

The induction decreases the query path. Ordinary branches use actual child
lookups. Closed binders stop before unfolding. The constructor heap stays
unchanged. No unfolding cost heap or original construction is required.
-/
namespace MicroCFTA.SourceClosedGateComplete
open InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open InternedFreshOrdinaryStatefulGateTrace EqualityNormalize

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Every closed available node has a complete query graph at its original heap. -/
theorem node (unconstrained : Value Symbol Guard → Bool) (path : Path)
    (value : Value Symbol Guard) (state : State Symbol Guard)
    (facts : Facts state) (available : Available state value) (closed : value.free = []) :
    ∃ answer, NodeTrace unconstrained path value state answer state := by
  induction path generalizing value with
  | nil =>
      cases value with
      | empty => exact ⟨false, .empty⟩
      | reference name => simp [Value.free] at closed
      | union entry members depth free => exact ⟨true, .union members⟩
      | mu entry body depth ordinary =>
          cases plain : unconstrained (.mu entry body depth ordinary) with
          | false => exact ⟨true, .constrained plain⟩
          | true => exact ⟨false, .closed plain (by rw [closed]; rfl)⟩
      | node entry edges depth free =>
          cases fast : depth == 0 && free.isEmpty with
          | true => exact ⟨false, .finite fast⟩
          | false => exact ⟨!free.isEmpty, .endpoint fast⟩
  | cons index rest ih =>
      cases value with
      | empty => exact ⟨false, .empty⟩
      | reference name => simp [Value.free] at closed
      | union entry members depth free => exact ⟨true, .union members⟩
      | mu entry body depth ordinary =>
          cases plain : unconstrained (.mu entry body depth ordinary) with
          | false => exact ⟨true, .constrained plain⟩
          | true => exact ⟨false, .closed plain (by rw [closed]; rfl)⟩
      | node entry edges depth free =>
          cases fast : depth == 0 && free.isEmpty with
          | true => exact ⟨false, .finite fast⟩
          | false =>
              have resident : Edges state edges := InternedEdgeResidency.resident_edges state facts.linked
                (.node entry edges depth free) available.resident
              have shut : ClosedEdges edges := MergedColdReaderClosed.node_children_closed state facts
                entry edges depth free available closed
              have scan : ∀ scanEdges : List (EdgeValue Symbol Guard), Edges state scanEdges → ClosedEdges scanEdges →
                  ∃ answer, EdgesTrace unconstrained index rest scanEdges state answer state := by
                intro scanEdges resident shut
                induction scanEdges with
                | nil => exact ⟨false, .nil⟩
                | cons edge tail tailIH =>
                    have headAvailable := facts.cached.edges _ _ (resident _ List.mem_cons_self)
                    have headClosed := shut _ List.mem_cons_self
                    have head : ∃ answer, ChildTrace unconstrained edge.children index rest state answer state := by
                      cases found : edge.children[index]? with
                      | none => exact ⟨false, .missing found⟩
                      | some child =>
                          have member := List.mem_of_getElem? found
                          obtain ⟨answer, trace⟩ := ih child (headAvailable _ member) (headClosed _ member)
                          exact ⟨answer, .present found trace⟩
                    obtain ⟨answer, head⟩ := head
                    cases answer with
                    | true => exact ⟨true, .stop head⟩
                    | false =>
                        obtain ⟨answer, trace⟩ := tailIH
                          (fun edge member => resident edge (List.mem_cons_of_mem _ member))
                          (fun edge member => shut edge (List.mem_cons_of_mem _ member))
                        exact ⟨answer, .next head trace⟩
              obtain ⟨answer, trace⟩ := scan edges resident shut
              exact ⟨answer, .branches fast trace⟩

/-- Actual child lookup derives a complete query without a supplied node trace. -/
theorem child (unconstrained : Value Symbol Guard → Bool) (values : List (Value Symbol Guard))
    (index : Nat) (path : Path) (state : State Symbol Guard)
    (facts : Facts state) (available : Values state values) (closed : ClosedValues values) :
    ∃ answer, ChildTrace unconstrained values index path state answer state := by
  cases found : values[index]? with
  | none => exact ⟨false, .missing found⟩
  | some value =>
      have member := List.mem_of_getElem? found
      obtain ⟨answer, trace⟩ := node unconstrained path value state facts (available _ member) (closed _ member)
      exact ⟨answer, .present found trace⟩

/-- Every finite path query on a closed forest completes at the original heap. -/
theorem path (unconstrained : Value Symbol Guard → Bool) (values : List (Value Symbol Guard))
    (position : Path) (state : State Symbol Guard)
    (facts : Facts state) (available : Values state values) (closed : ClosedValues values) :
    ∃ answer, PathTrace unconstrained values position state answer state := by
  cases position with
  | nil => exact ⟨false, .empty⟩
  | cons index rest =>
      obtain ⟨answer, trace⟩ := child unconstrained values index rest state facts available closed
      exact ⟨answer, .child trace⟩

/-- Ordered class short circuit completes without visiting paths after a true result. -/
theorem classes (unconstrained : Value Symbol Guard → Bool) (values : List (Value Symbol Guard))
    (paths : Class) (state : State Symbol Guard)
    (facts : Facts state) (available : Values state values) (closed : ClosedValues values) :
    ∃ answer, ClassTrace unconstrained values paths state answer state := by
  induction paths with
  | nil => exact ⟨false, .nil⟩
  | cons position rest ih =>
      obtain ⟨answer, trace⟩ := path unconstrained values position state facts available closed
      cases answer with
      | true => exact ⟨true, .stop trace⟩
      | false =>
          obtain ⟨answer, tail⟩ := ih
          exact ⟨answer, .next trace tail⟩

/-- Every finite ordered selection has a complete graph on a closed available forest. -/
theorem selection (unconstrained : Value Symbol Guard → Bool) (values : List (Value Symbol Guard))
    (constraints : Constraints) (state : State Symbol Guard)
    (facts : Facts state) (available : Values state values) (closed : ClosedValues values) :
    ∃ queries, InternedSourceClassSelection.Trace unconstrained values constraints state queries state := by
  induction constraints with
  | nil => exact ⟨[], .nil⟩
  | cons paths rest ih =>
      obtain ⟨answer, head⟩ := classes unconstrained values paths state facts available closed
      obtain ⟨queries, tail⟩ := ih
      exact ⟨_, .cons head tail⟩

end MicroCFTA.SourceClosedGateComplete
