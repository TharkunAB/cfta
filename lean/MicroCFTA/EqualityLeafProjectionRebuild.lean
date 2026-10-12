import MicroCFTA.EqualityLeafProjectionPhysical

/-!
# Completed physical parent-edge rebuilding

The source interns each rebuilt ancestor edge after its ordered children
are ready. Executing these requests supplies the resident output records
needed by the normalization correspondence. Replay uses the final actual
cache rather than a supplied pure edge identity function.
-/
namespace MicroCFTA.EqualityLeafProjectionPhysical
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedFreshProbeKeys InternedEdgeResidency InternedNodeSetCongruence
open EqualityLeafProjectionSyntax

/-- The actual edge request preserves symbol, guard, and ordered edited children. -/
def rebuildWork (change : Nat → Value Symbol Guard → Value Symbol Guard) (edge : EdgeValue Symbol Guard) :
    Work Symbol Guard (EdgeValue Symbol Guard) :=
  makeEdge edge.entry.key.symbol edge.entry.key.constraint (mapChildren change 0 edge.children)

/-- Complete the requested ancestor edges in their original occurrence order. -/
def rebuildMany (change : Nat → Value Symbol Guard → Value Symbol Guard) :
    List (EdgeValue Symbol Guard) → Work Symbol Guard (List (EdgeValue Symbol Guard))
  | [] => .pure []
  | edge :: rest => (rebuildWork change edge).bind fun value =>
      (rebuildMany change rest).bind fun values => .pure (value :: values)

/-- Every rebuilt edge request carries its literal source constructor fields. -/
theorem rebuildMany_safe (change : Nat → Value Symbol Guard → Value Symbol Guard) (edges : List (EdgeValue Symbol Guard)) :
    Safe (rebuildMany change edges) := by
  induction edges with
  | nil => trivial
  | cons edge rest ih => exact safe_bind _ _ (makeEdge_safe _ _ _) (fun _ => safe_bind _ _ ih (fun _ => trivial))

/-- Edge interning itself returns a resident complete record. -/
theorem makeEdge_resident [DecidableEq (EdgeKey Symbol Guard)] (symbol : Symbol) (constraint : Guard)
    (children : List (Value Symbol Guard)) (state : State Symbol Guard) (coherent : Coherent state) :
    EdgeResident (run (makeEdge symbol constraint children) state).2 (run (makeEdge symbol constraint children) state).1 := by
  let key : EdgeKey Symbol Guard := ⟨symbol, children.map Value.referenceOf, constraint⟩
  let identify := fun entry => EdgeValue.mk entry children
  have correct := edgeStep_correct key identify state coherent.valid
  have after := edgeStep_coherent key identify state coherent (fun _ same => ⟨rfl, same, rfl⟩)
  have fields := (after.edges key _ correct.2.2).2.1
  change (edgeStep key identify state).2.edgeRecords (edgeStep key identify state).1.entry.key = some _
  rw [fields]
  exact correct.2.2

/-- Finite rebuilding derives output coherence, complete ordered readback, and
allocation-free replay of every original edge request in the resulting cache. -/
theorem rebuildMany_completed [DecidableEq (EdgeKey Symbol Guard)]
    (change : Nat → Value Symbol Guard → Value Symbol Guard) (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) :
    let result := run (rebuildMany change edges) state
    Coherent result.2 ∧ result.1 = edges.map (rebuild result.2 change) ∧
      ∀ edge ∈ edges, run (rebuildWork change edge) result.2 = (rebuild result.2 change edge, result.2) ∧
        EdgeResident result.2 (rebuild result.2 change edge) := by
  induction edges generalizing state with
  | nil => exact ⟨coherent, rfl, by simp⟩
  | cons edge rest ih =>
      let head := run (rebuildWork change edge) state
      let tail := run (rebuildMany change rest) head.2
      have headCoherent : Coherent head.2 := InternedErasedEdgeReplay.run_coherent (rebuildWork change edge) state
        (makeEdge_safe _ _ _) coherent
      have checked : Coherent tail.2 ∧ tail.1 = rest.map (rebuild tail.2 change) ∧
          ∀ original ∈ rest, run (rebuildWork change original) tail.2 = (rebuild tail.2 change original, tail.2) ∧
            EdgeResident tail.2 (rebuild tail.2 change original) := ih head.2 headCoherent
      have growth : Grows head.2 tail.2 := (InternedConstructorTemplates.run_correct (rebuildMany change rest) head.2 headCoherent.valid).2
      have repeated := replay (rebuildWork change edge) state tail.2 coherent.valid growth
      have projected := congrArg (fun result : EdgeValue Symbol Guard × State Symbol Guard => result.1) repeated
      have same : rebuild tail.2 change edge = head.1 := by
        simpa only [rebuild, rebuildWork, head] using projected
      have resident : EdgeResident head.2 head.1 := makeEdge_resident _ _ _ state coherent
      change Coherent (run (rebuildMany change (edge :: rest)) state).2 ∧ _
      simp only [rebuildMany, run_bind, run]
      change Coherent tail.2 ∧ head.1 :: tail.1 = (edge :: rest).map (rebuild tail.2 change) ∧
        ∀ original ∈ edge :: rest, run (rebuildWork change original) tail.2 = (rebuild tail.2 change original, tail.2) ∧
          EdgeResident tail.2 (rebuild tail.2 change original)
      refine ⟨checked.1, ?_, ?_⟩
      · simp only [List.map_cons, same, checked.2.1]
      · intro original present
        rcases List.mem_cons.mp present with originalSame | member
        · subst original
          refine ⟨?_, ?_⟩
          · exact repeated.trans (congrArg (fun value => (value, tail.2)) same.symm)
          · rw [same]
            exact edge_grows head.2 tail.2 growth head.1 resident
        · exact checked.2.2 original member

/-- Actual completed edge requests discharge the normalization adapter's
output-residency premise. Required-path filtering can select any subset. -/
theorem completed_readback [DecidableEq (EdgeKey Symbol Guard)]
    (before state : State Symbol Guard) (beforeCoherent : Coherent before) (linked : Linked before)
    (coherent : Coherent state) (edges : List (EdgeValue Symbol Guard))
    (resident : ∀ edge ∈ edges, EdgeResident before edge)
    (select : EdgeValue Symbol Guard → Bool) (change : Nat → Value Symbol Guard → Value Symbol Guard)
    (empty : ∀ index, change index .empty = .empty) :
    let after := (run (rebuildMany change edges) state).2
    makeNode ((edges.filter select).map (rebuild after change)) =
      makeNode (((nodeEdges (run (makeNode edges) before).1).filter select).map (rebuild after change)) := by
  let after := (run (rebuildMany change edges) state).2
  have completed := rebuildMany_completed change edges state coherent
  exact rebuild_readback before after after beforeCoherent linked completed.1 completed.1 edges resident select change empty
    (fun edge member => (completed.2.2 edge member).2)

/-- With every original row selected, completed requests give the physical
constructor equation for path editing below an ordinary node. -/
theorem completed_edit_readback [DecidableEq (EdgeKey Symbol Guard)]
    (before state : State Symbol Guard) (beforeCoherent : Coherent before) (linked : Linked before)
    (coherent : Coherent state) (edges : List (EdgeValue Symbol Guard))
    (resident : ∀ edge ∈ edges, EdgeResident before edge)
    (change : Nat → Value Symbol Guard → Value Symbol Guard)
    (empty : ∀ index, change index .empty = .empty) :
    let after := (run (rebuildMany change edges) state).2
    makeNode (edges.map (rebuild after change)) =
      makeNode ((nodeEdges (run (makeNode edges) before).1).map (rebuild after change)) := by
  have keep (values : List (EdgeValue Symbol Guard)) : values.filter (fun _ => true) = values :=
    List.filter_eq_self.mpr (fun _ _ => rfl)
  simpa only [keep] using completed_readback before state beforeCoherent linked coherent
    edges resident (fun _ => true) change empty

/-- Required-path filtering uses the original actual child arity before the
completed recursive child requirements rebuild each retained edge. -/
theorem completed_require_readback [DecidableEq (EdgeKey Symbol Guard)]
    (before state : State Symbol Guard) (beforeCoherent : Coherent before) (linked : Linked before)
    (coherent : Coherent state) (paths : List Path) (edges : List (EdgeValue Symbol Guard))
    (resident : ∀ edge ∈ edges, EdgeResident before edge)
    (change : Nat → Value Symbol Guard → Value Symbol Guard)
    (empty : ∀ index, change index .empty = .empty) :
    let after := (run (rebuildMany change edges) state).2
    makeNode ((edges.filter (fun edge => fits paths edge.children.length)).map (rebuild after change)) =
      makeNode (((nodeEdges (run (makeNode edges) before).1).filter
        (fun edge => fits paths edge.children.length)).map (rebuild after change)) :=
  completed_readback before state beforeCoherent linked coherent edges resident
    (fun edge => fits paths edge.children.length) change empty

end MicroCFTA.EqualityLeafProjectionPhysical
