import MicroCFTA.EqualityLeafProjectionWorkerReadback

/-!
# Prepared finite caches for original parent occurrences

The cache preparation executes the selected original child requests and
then the original rebuilt edge requests. Later cache growth preserves
those results. Actual child readbacks in the later cache therefore give
the same normalized parent request as the stored canonical source rows.
-/
namespace MicroCFTA.EqualityLeafProjectionParentCache
open InternedConstructorTemplates InternedRecordCoherence InternedEdgeResidency InternedProbeProvenance
open EqualityLeafProjectionSyntax (mapChildren)
open EqualityLeafProjectionWorkers EqualityLeafProjectionPhysical

/-- A finite completed request sequence replays every member after later cache growth. -/
theorem sequence_replay_grows [DecidableEq (EdgeKey Symbol Guard)]
    (requests : List (Work Symbol Guard Result)) (before after : State Symbol Guard)
    (valid : InternedConstructorTemplates.Valid before)
    (growth : Grows (run (sequence requests) before).2 after)
    (request : Work Symbol Guard Result) (member : request ∈ requests) :
    run request after = ((run request (run (sequence requests) before).2).1, after) := by
  let completed := run (sequence requests) before
  have closed := (sequence_completed requests before valid).2 request member
  have completedValid : InternedConstructorTemplates.Valid completed.2 :=
    (InternedConstructorTemplates.run_correct _ before valid).1
  have requestGrowth : Grows (run request completed.2).2 after := by
    rw [closed]
    exact growth
  exact replay request completed.2 after completedValid requestGrowth

/-- Positional equality on actual original occurrences determines the ordered child map. -/
theorem mapChildren_congr (first second : Nat → Value Symbol Guard → Value Symbol Guard)
    (index : Nat) (children : List (Value Symbol Guard))
    (same : ∀ position child, (position, child) ∈ indexed index children → first position child = second position child) :
    mapChildren first index children = mapChildren second index children := by
  induction children generalizing index with
  | nil => rfl
  | cons child rest ih =>
      rw [mapChildren, mapChildren, same index child (by simp [indexed])]
      congr 1
      apply ih
      intro position selected member
      exact same position selected (by simp only [indexed, List.mem_cons]; exact Or.inr member)

/-- Read an actual optional child worker after its finite completion. -/
def change [DecidableEq (EdgeKey Symbol Guard)]
    (request : Nat → Value Symbol Guard → Work Symbol Guard (Option (Value Symbol Guard)))
    (state : State Symbol Guard) (index : Nat) (child : Value Symbol Guard) : Value Symbol Guard :=
  workerValue (request index child) state

/-- Later child readback agrees on every selected original child occurrence. -/
theorem child_map_grows [DecidableEq (EdgeKey Symbol Guard)]
    (request : Nat → Value Symbol Guard → Work Symbol Guard (Option (Value Symbol Guard)))
    (edges : List (EdgeValue Symbol Guard)) (before after : State Symbol Guard)
    (valid : InternedConstructorTemplates.Valid before)
    (growth : Grows (run (sequence (childRequests request edges)) before).2 after)
    (edge : EdgeValue Symbol Guard) (member : edge ∈ edges) :
    mapChildren (change request after) 0 edge.children =
      mapChildren (change request (run (sequence (childRequests request edges)) before).2) 0 edge.children := by
  apply mapChildren_congr
  intro index child position
  have repeated := sequence_replay_grows (childRequests request edges) before after valid growth
    (request index child) (childRequests_member request edges edge member index child position)
  simp only [change, workerValue, repeated]

/-- Actual edge preparation makes every original rebuilt row available in all later caches. -/
theorem rebuilt_grows [DecidableEq (EdgeKey Symbol Guard)]
    (edges : List (EdgeValue Symbol Guard)) (change : Nat → Value Symbol Guard → Value Symbol Guard)
    (before after : State Symbol Guard) (coherent : Coherent before)
    (growth : Grows (run (rebuildMany change edges) before).2 after)
    (edge : EdgeValue Symbol Guard) (member : edge ∈ edges) :
    rebuild after change edge = rebuild (run (rebuildMany change edges) before).2 change edge ∧
      EdgeResident after (rebuild after change edge) := by
  let completed := run (rebuildMany change edges) before
  have prepared := rebuildMany_completed change edges before coherent
  have closed := (prepared.2.2 edge member).1
  have requestGrowth : Grows (run (rebuildWork change edge) completed.2).2 after := by
    rw [closed]
    exact growth
  have repeated := replay (rebuildWork change edge) completed.2 after prepared.1.valid requestGrowth
  have same : rebuild after change edge = rebuild completed.2 change edge := by
    have projected := congrArg (fun result : EdgeValue Symbol Guard × State Symbol Guard => result.1) repeated
    simpa only [closed, rebuildWork, rebuild] using projected
  exact ⟨same, same ▸ edge_grows completed.2 after growth _ (prepared.2.2 edge member).2⟩

/-- Executing the finite original requests derives parent normalization at the
actual later child-readback state. This does not require a globally closed cache. -/
theorem prepared_parent [DecidableEq (EdgeKey Symbol Guard)]
    (request : Nat → Value Symbol Guard → Work Symbol Guard (Option (Value Symbol Guard)))
    (safe : ∀ index child, Safe (request index child))
    (empty : ∀ index, request index .empty = .pure (some .empty))
    (edges : List (EdgeValue Symbol Guard)) (select : EdgeValue Symbol Guard → Bool)
    (before current after : State Symbol Guard) (beforeCoherent : Coherent before) (linked : Linked before)
    (currentCoherent : Coherent current) (afterCoherent : Coherent after)
    (resident : ∀ edge ∈ edges, EdgeResident before edge)
    (growth : Grows
      (run (rebuildMany (change request (run (sequence (childRequests request (edges.filter select))) current).2) edges)
        (run (sequence (childRequests request (edges.filter select))) current).2).2 after) :
    makeNode ((edges.filter select).map (rebuild after (change request after))) =
      makeNode (((nodeEdges (run (makeNode edges) before).1).filter select).map (rebuild after (change request after))) := by
  let children := (run (sequence (childRequests request (edges.filter select))) current).2
  let initialChange := change request children
  let prepared := run (rebuildMany initialChange edges) children
  have childrenCoherent : Coherent children := InternedErasedEdgeReplay.run_coherent _ current
    (sequence_safe _ (childRequests_safe request safe _)) currentCoherent
  have childrenGrowth : Grows children after := grows_trans
    (InternedConstructorTemplates.run_correct (rebuildMany initialChange edges) children childrenCoherent.valid).2 growth
  have changedResident : ∀ edge ∈ edges, EdgeResident after (rebuild after initialChange edge) :=
    fun edge member => (rebuilt_grows edges initialChange children after childrenCoherent growth edge member).2
  have changeEmpty : ∀ index, initialChange index .empty = .empty := by
    intro index
    simp only [initialChange, change, workerValue, empty, run, Option.getD_some]
  have normalized := rebuild_readback before after after beforeCoherent linked afterCoherent afterCoherent
    edges resident select initialChange changeEmpty changedResident
  have edgeSame : ∀ edge ∈ edges.filter select, rebuild after (change request after) edge = rebuild after initialChange edge := by
    intro edge member
    unfold rebuild
    rw [child_map_grows request (edges.filter select) current after currentCoherent.valid childrenGrowth edge member]
  have leftSame : (edges.filter select).map (rebuild after (change request after)) =
      (edges.filter select).map (rebuild after initialChange) := List.map_congr_left edgeSame
  have rightSame : ((nodeEdges (run (makeNode edges) before).1).filter select).map (rebuild after (change request after)) =
      ((nodeEdges (run (makeNode edges) before).1).filter select).map (rebuild after initialChange) := by
    apply List.map_congr_left
    intro edge member
    have selected := List.mem_filter.mp member
    have original := selected.1
    rw [makeNode_edges edges before beforeCoherent linked resident] at original
    exact edgeSame edge (List.mem_filter.mpr ⟨(List.mem_filter.mp (canonicalEdges_member _ edge original)).1, selected.2⟩)
  rw [leftSame, rightSame]
  exact normalized

/-- Prepare only the selected child requests, then every original ancestor edge request. -/
def prepare [DecidableEq (EdgeKey Symbol Guard)]
    (request : Nat → Value Symbol Guard → Work Symbol Guard (Option (Value Symbol Guard)))
    (select : EdgeValue Symbol Guard → Bool) (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) : State Symbol Guard :=
  let children := (run (sequence (childRequests request (edges.filter select))) state).2
  (run (rebuildMany (change request children) edges) children).2

/-- Finite preparation derives a coherent cache that retains its input records. -/
theorem prepare_correct [DecidableEq (EdgeKey Symbol Guard)]
    (request : Nat → Value Symbol Guard → Work Symbol Guard (Option (Value Symbol Guard)))
    (safe : ∀ index child, Safe (request index child))
    (select : EdgeValue Symbol Guard → Bool) (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) :
    Coherent (prepare request select edges state) ∧ Grows state (prepare request select edges state) := by
  let children := (run (sequence (childRequests request (edges.filter select))) state).2
  have childrenCoherent : Coherent children := InternedErasedEdgeReplay.run_coherent _ state
    (sequence_safe _ (childRequests_safe request safe _)) coherent
  exact ⟨InternedErasedEdgeReplay.run_coherent _ children (rebuildMany_safe _ edges) childrenCoherent,
    grows_trans (InternedConstructorTemplates.run_correct _ state coherent.valid).2
      (InternedConstructorTemplates.run_correct _ children childrenCoherent.valid).2⟩

end MicroCFTA.EqualityLeafProjectionParentCache
