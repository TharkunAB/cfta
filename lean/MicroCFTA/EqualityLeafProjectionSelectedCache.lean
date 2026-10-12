import MicroCFTA.EqualityLeafProjectionRequireSyntax

/-!
# Selected-row finite parent preparation

Required-path preparation constructs only selected original rows. The
normalization proof keeps each unselected original edge unchanged. This
avoids rebuilding a discarded row with an uncompleted child readback.
-/
namespace MicroCFTA.EqualityLeafProjectionSelectedCache
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance InternedEdgeResidency
open EqualityLeafProjectionWorkers EqualityLeafProjectionPhysical EqualityLeafProjectionParentCache

/-- Prepare selected original child requests and only their selected parent edge requests. -/
def prepare [DecidableEq (EdgeKey Symbol Guard)]
    (request : Nat → Value Symbol Guard → Work Symbol Guard (Option (Value Symbol Guard)))
    (select : EdgeValue Symbol Guard → Bool) (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard) : State Symbol Guard :=
  let selected := edges.filter select
  let children := (run (sequence (childRequests request selected)) state).2
  (run (rebuildMany (change request children) selected) children).2

/-- Selected finite preparation retains coherence and the earlier cache records. -/
theorem prepare_correct [DecidableEq (EdgeKey Symbol Guard)]
    (request : Nat → Value Symbol Guard → Work Symbol Guard (Option (Value Symbol Guard)))
    (safe : ∀ index child, Safe (request index child))
    (select : EdgeValue Symbol Guard → Bool) (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) :
    Coherent (prepare request select edges state) ∧ Grows state (prepare request select edges state) := by
  let selected := edges.filter select
  let children := (run (sequence (childRequests request selected)) state).2
  have childrenCoherent : Coherent children := InternedErasedEdgeReplay.run_coherent _ state
    (sequence_safe _ (childRequests_safe request safe _)) coherent
  exact ⟨InternedErasedEdgeReplay.run_coherent _ children (rebuildMany_safe _ selected) childrenCoherent,
    grows_trans (InternedConstructorTemplates.run_correct _ state coherent.valid).2
      (InternedConstructorTemplates.run_correct _ children childrenCoherent.valid).2⟩

/-- Selected finite preparation derives normalized parent reconstruction without
constructing any discarded original edge or its unselected child result. -/
theorem prepared_parent [DecidableEq (EdgeKey Symbol Guard)]
    (request : Nat → Value Symbol Guard → Work Symbol Guard (Option (Value Symbol Guard)))
    (safe : ∀ index child, Safe (request index child))
    (empty : ∀ index, request index .empty = .pure (some .empty))
    (edges : List (EdgeValue Symbol Guard)) (select : EdgeValue Symbol Guard → Bool)
    (before current after : State Symbol Guard) (beforeCoherent : Coherent before) (linked : Linked before)
    (currentCoherent : Coherent current) (afterCoherent : Coherent after)
    (resident : ∀ edge ∈ edges, EdgeResident before edge)
    (originalGrowth : Grows before after) (growth : Grows (prepare request select edges current) after) :
    makeNode ((edges.filter select).map (rebuild after (change request after))) =
      makeNode (((nodeEdges (run (makeNode edges) before).1).filter select).map (rebuild after (change request after))) := by
  let selected := edges.filter select
  let children := (run (sequence (childRequests request selected)) current).2
  let earlier := change request children
  have childrenCoherent : Coherent children := InternedErasedEdgeReplay.run_coherent _ current
    (sequence_safe _ (childRequests_safe request safe _)) currentCoherent
  have childrenGrowth : Grows children after := grows_trans
    (InternedConstructorTemplates.run_correct (rebuildMany earlier selected) children childrenCoherent.valid).2 growth
  have selectedResident : ∀ edge ∈ selected, EdgeResident after (rebuild after (change request after) edge) := by
    intro edge member
    have same : rebuild after (change request after) edge = rebuild after earlier edge := by
      unfold rebuild
      rw [child_map_grows request selected current after currentCoherent.valid childrenGrowth edge member]
    rw [same]
    exact (rebuilt_grows selected earlier children after childrenCoherent growth edge member).2
  let changed := fun edge => if select edge then rebuild after (change request after) edge else edge
  have changedResident : ∀ edge ∈ edges, EdgeResident after (changed edge) := by
    intro edge member
    dsimp only [changed]
    split
    · exact selectedResident edge (List.mem_filter.mpr ⟨member, ‹_›⟩)
    · exact edge_grows before after originalGrowth edge (resident edge member)
  have changeEmpty : ∀ index, change request after index .empty = .empty := by
    intro index
    simp only [change, workerValue, empty, run, Option.getD_some]
  have preservesDead : ∀ edge ∈ edges, dead edge = true → dead (changed edge) = true := by
    intro edge _ isDead
    dsimp only [changed]
    split
    · exact rebuild_dead after afterCoherent (change request after) changeEmpty edge isDead
    · exact isDead
  have normalized := mapped_readback before after beforeCoherent linked afterCoherent edges resident select changed changedResident preservesDead
  have exactMap : ∀ rows : List (EdgeValue Symbol Guard), (rows.filter select).map changed =
      (rows.filter select).map (rebuild after (change request after)) := by
    intro rows
    apply List.map_congr_left
    intro edge member
    exact ite_eq_left (List.mem_filter.mp member).2
  rw [exactMap, exactMap] at normalized
  exact normalized

end MicroCFTA.EqualityLeafProjectionSelectedCache
