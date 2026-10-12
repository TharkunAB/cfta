import MicroCFTA.EqualityLeafProjectionSelectedCache

/-!
# Complete payloads in selected finite proof preparation

Each selected original child request runs on available complete inputs.
Its completed readback is available in the shared child cache. Rebuilding
only selected ancestor rows therefore preserves stored child availability
and node-edge links as well as coherence.
-/
namespace MicroCFTA.EqualityLeafProjectionPreparationAvailability
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance InternedEdgeResidency
open EqualityLeafProjectionSyntax (mapChildren)
open EqualityLeafProjectionCompileAvailability EqualityLeafProjectionWorkers
open EqualityLeafProjectionRequireAvailability EqualityLeafProjectionPhysical EqualityLeafProjectionParentCache

/-- Local child requests preserve complete cache facts and successful payloads. -/
def RequestAvailable [DecidableEq (EdgeKey Symbol Guard)]
    (request : Nat → Value Symbol Guard → Work Symbol Guard (Option (Value Symbol Guard))) : Prop :=
  ∀ index child state, Facts state → Available state child → Checked Available (request index child) state

/-- Sequential indexed requests preserve complete cache facts through every original position. -/
theorem indexed_requests_facts [DecidableEq (EdgeKey Symbol Guard)]
    (request : Nat → Value Symbol Guard → Work Symbol Guard (Option (Value Symbol Guard)))
    (requestsAvailable : RequestAvailable request) (positions : List (Nat × Value Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state)
    (inputs : ∀ position ∈ positions, Available state position.2) :
    Facts (run (sequence (positions.map fun position => request position.1 position.2)) state).2 := by
  induction positions generalizing state with
  | nil => exact facts
  | cons first rest ih =>
      have checked := requestsAvailable first.1 first.2 state facts (inputs first (by simp))
      have tailInputs : ∀ position ∈ rest, Available (run (request first.1 first.2) state).2 position.2 := by
        intro position member
        exact available_after_run (request first.1 first.2) state facts.coherent.valid (inputs position (by simp [member]))
      have tail := ih _ checked.1 tailInputs
      simpa only [List.map_cons, sequence, run_bind, run] using tail

/-- The actual source position sequence covers exactly the original ordered children. -/
theorem child_requests_facts [DecidableEq (EdgeKey Symbol Guard)]
    (request : Nat → Value Symbol Guard → Work Symbol Guard (Option (Value Symbol Guard)))
    (requestsAvailable : RequestAvailable request) (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state)
    (inputs : ∀ edge ∈ edges, ChildrenAvailable state edge.children) :
    Facts (run (sequence (childRequests request edges)) state).2 := by
  let positions := edges.flatMap fun edge => indexed 0 edge.children
  have inputs : ∀ position ∈ positions, Available state position.2 := by
    intro position member
    obtain ⟨edge, included, found⟩ := List.mem_flatMap.mp member
    exact inputs edge included position.2 (indexed_member 0 position.1 edge.children position.2 found)
  have checked := indexed_requests_facts request requestsAvailable positions state facts inputs
  simpa only [positions, childRequests, List.map_flatMap] using checked

/-- Every completed original child readback is available, including the explicit empty fallback. -/
theorem child_readback_available [DecidableEq (EdgeKey Symbol Guard)]
    (request : Nat → Value Symbol Guard → Work Symbol Guard (Option (Value Symbol Guard)))
    (requestsAvailable : RequestAvailable request) (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state)
    (inputs : ∀ edge ∈ edges, ChildrenAvailable state edge.children)
    (edge : EdgeValue Symbol Guard) (member : edge ∈ edges) (index : Nat) (child : Value Symbol Guard)
    (position : (index, child) ∈ indexed 0 edge.children) :
    let completed := (run (sequence (childRequests request edges)) state).2
    Available completed (change request completed index child) := by
  let completed := (run (sequence (childRequests request edges)) state).2
  have completedFacts := child_requests_facts request requestsAvailable edges state facts inputs
  have original := inputs edge member child (indexed_member 0 index edge.children child position)
  have laterInput := available_after_run (sequence (childRequests request edges)) state facts.coherent.valid original
  have checked := requestsAvailable index child completed completedFacts laterInput
  have closed := (sequence_completed (childRequests request edges) state facts.coherent.valid).2
    (request index child) (childRequests_member request edges edge member index child position)
  have stateSame := congrArg (fun result : Option (Value Symbol Guard) × State Symbol Guard => result.2) closed
  change Available completed ((run (request index child) completed).1.getD .empty)
  cases found : (run (request index child) completed).1 with
  | none =>
      simp only [Option.getD_none]
      exact empty_available completed
  | some value =>
      simp only [Option.getD_some]
      have available := checked.2 value found
      rw [stateSame] at available
      exact available

/-- Available values at each actual position give an available ordered mapped child list. -/
theorem mapped_children_available (change : Nat → Value Symbol Guard → Value Symbol Guard)
    (state : State Symbol Guard) (index : Nat) (children : List (Value Symbol Guard))
    (available : ∀ position child, (position, child) ∈ indexed index children → Available state (change position child)) :
    ChildrenAvailable state (mapChildren change index children) := by
  induction children generalizing index with
  | nil => simp [mapChildren, ChildrenAvailable]
  | cons child rest ih =>
      intro value member
      simp only [mapChildren, List.mem_cons] at member
      rcases member with same | later
      · subst value
        exact available index child (by simp [indexed])
      · apply ih (index + 1) _ value later
        intro position selected present
        exact available position selected (by simp only [indexed, List.mem_cons]; exact Or.inr present)

/-- Rebuilding completed available child maps preserves every complete parent cache invariant. -/
theorem rebuild_many_facts [DecidableEq (EdgeKey Symbol Guard)]
    (change : Nat → Value Symbol Guard → Value Symbol Guard) (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state)
    (inputs : ∀ edge ∈ edges, ChildrenAvailable state (mapChildren change 0 edge.children)) :
    Facts (run (rebuildMany change edges) state).2 := by
  induction edges generalizing state with
  | nil => exact facts
  | cons edge rest ih =>
      have available := makeEdge_available edge.entry.key.symbol edge.entry.key.constraint
        (mapChildren change 0 edge.children) state facts.coherent facts.cached (inputs edge (by simp))
      have linked := makeEdge_linked edge.entry.key.symbol edge.entry.key.constraint
        (mapChildren change 0 edge.children) state facts.coherent facts.linked
      have nextFacts : Facts (run (rebuildWork change edge) state).2 := ⟨available.1, available.2.1, linked.1⟩
      have nextInputs : ∀ other ∈ rest, ChildrenAvailable (run (rebuildWork change edge) state).2
          (mapChildren change 0 other.children) := by
        intro other member value present
        exact available_after_run (rebuildWork change edge) state facts.coherent.valid (inputs other (by simp [member]) value present)
      have tail := ih _ nextFacts nextInputs
      simpa only [rebuildMany, run_bind, run] using tail

/-- Selected-only preparation derives full Facts from actual child-worker payload preservation. -/
theorem prepare_facts [DecidableEq (EdgeKey Symbol Guard)]
    (request : Nat → Value Symbol Guard → Work Symbol Guard (Option (Value Symbol Guard)))
    (requestsAvailable : RequestAvailable request) (select : EdgeValue Symbol Guard → Bool)
    (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard) (facts : Facts state)
    (inputs : ∀ edge ∈ edges, ChildrenAvailable state edge.children) :
    Facts (EqualityLeafProjectionSelectedCache.prepare request select edges state) := by
  let selected := edges.filter select
  let children := (run (sequence (childRequests request selected)) state).2
  have selectedInputs : ∀ edge ∈ selected, ChildrenAvailable state edge.children :=
    fun edge member => inputs edge (List.mem_filter.mp member).1
  have childrenFacts := child_requests_facts request requestsAvailable selected state facts selectedInputs
  apply rebuild_many_facts (change request children) selected children childrenFacts
  intro edge member
  apply mapped_children_available
  intro index child position
  exact child_readback_available request requestsAvailable selected state facts selectedInputs edge member index child position

end MicroCFTA.EqualityLeafProjectionPreparationAvailability
