import MicroCFTA.SourcePhysicalRecursiveRows

/-!
# Exact physical rows after one-knot unfolding

The nullary row survives normalization. The unary row retains the exact
complete Mu record as its child. Actual canonical edge residency determines
both cache-hit readback and the node's sorted edge list.
-/
namespace MicroCFTA.SourcePhysicalRecursiveRows
open InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedProvenance InternedEdgeResidency
open InternedNestedConstruction (Outcome work)

/-- Exact physical constructor shape and its two stored alternatives. -/
structure Exposed (root result : Value Symbol Unit) (base step : Symbol) : Prop where
  ordinary : ∃ entry edges depth free, result = .node entry edges depth free
  rows : ∃ first second : EdgeValue Symbol Unit,
    first.entry.key.symbol = base ∧ first.children = [] ∧
    second.entry.key.symbol = step ∧ second.children = [root] ∧
    nodeEdges result = canonicalEdges [first, second] ∧
    ∀ edge, edge ∈ nodeEdges result ↔ edge = first ∨ edge = second

/-- The actual sequence of two edges and node interning derives complete result rows. -/
theorem rebuild_checked [DecidableEq Symbol] (root : Value Symbol Unit) (base step : Symbol)
    (state : State Symbol Unit) (facts : Facts state) (available : Available state root)
    (nonempty : root.referenceOf ≠ .empty) :
    let result := run (rebuild root base step) state
    Facts result.2 ∧ Available result.2 result.1 ∧ Exposed root result.1 base step := by
  let first := run (makeEdge base () []) state
  have firstChecked := edge_verified base () [] state facts (by intro child member; cases member)
  have firstFacts : Facts first.2 := firstChecked.facts
  have firstResident : EdgeResident first.2 first.1 := firstChecked.result _ _ rfl
  have rootAfter : Available first.2 root := firstChecked.available root available
  let second := run (makeEdge step () [root]) first.2
  have secondChecked := edge_verified step () [root] first.2 firstFacts (by
    intro value member; rw [List.mem_singleton.mp member]; exact rootAfter)
  have secondFacts : Facts second.2 := secondChecked.facts
  have secondResident : EdgeResident second.2 second.1 := secondChecked.result _ _ rfl
  have firstLater : EdgeResident second.2 first.1 := edge_grows first.2 second.2 secondChecked.growth first.1 firstResident
  have resident : Edges second.2 [first.1, second.1] := by
    intro edge member
    rcases List.mem_cons.mp member with rfl | member
    · exact firstLater
    · rw [List.mem_singleton.mp member]; exact secondResident
  have firstFields := MergedPhysicalGroupEdges.makeEdge_fields state facts base () [] (by simp [Values])
  have secondFields := MergedPhysicalGroupEdges.makeEdge_fields first.2 firstFacts step () [root] (by
    intro value member; rw [List.mem_singleton.mp member]; exact rootAfter)
  have firstChildren : first.1.children = [] := firstFields.2.2
  have secondChildren : second.1.children = [root] := secondFields.2.2
  have liveFirst : EqualityLeafProjectionPhysical.dead first.1 = false := by
    simp only [EqualityLeafProjectionPhysical.dead, firstChildren, List.any_nil]
  have liveSecond : EqualityLeafProjectionPhysical.dead second.1 = false := by
    simp only [EqualityLeafProjectionPhysical.dead, secondChildren, List.any_cons, List.any_nil, Bool.or_false]
    exact beq_eq_false_iff_ne.mpr nonempty
  have surviving : InternedConstructorTemplates.surviving [first.1, second.1] = [first.1, second.1] := by
    simp only [InternedConstructorTemplates.surviving, List.filter_cons,
      show first.1.children.any (fun child => child.referenceOf == .empty) = false from liveFirst,
      show second.1.children.any (fun child => child.referenceOf == .empty) = false from liveSecond,
      Bool.not_false, ↓reduceIte, List.filter_nil]
  let result := run (makeNode [first.1, second.1]) second.2
  have checked := node_verified [first.1, second.1] second.2 secondFacts resident
  have readback : nodeEdges result.1 = canonicalEdges [first.1, second.1] := by
    rw [EqualityLeafProjectionPhysical.makeNode_edges _ _ secondFacts.coherent secondFacts.linked resident, surviving]
  have members : ∀ edge, edge ∈ nodeEdges result.1 ↔ edge = first.1 ∨ edge = second.1 := by
    intro edge
    rw [EqualityLeafProjectionPhysical.makeNode_edges _ _ secondFacts.coherent secondFacts.linked resident,
      EqualityLeafProjectionPhysical.normalized_member second.2 secondFacts.coherent _ resident edge]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · exact And.left
    · intro member
      exact ⟨member, by rcases member with rfl | rfl; exact liveFirst; exact liveSecond⟩
  have ordinary : ∃ entry edges depth free, result.1 = .node entry edges depth free := by
    have present := (members first.1).mpr (Or.inl rfl)
    cases found : result.1 <;> simp only [found, nodeEdges] at present <;> try contradiction
    case node entry edges depth free => exact ⟨entry, edges, depth, free, rfl⟩
  simp only [rebuild, run_bind]
  exact ⟨checked.facts, checked.result _ _ rfl, ordinary,
    ⟨first.1, second.1, firstFields.1, firstFields.2.2, secondFields.1, secondFields.2.2, readback, members⟩⟩

/-- Current closed one-knot unfolding completes with derived actual rows and both retained cache histories. -/
theorem unfold_complete [DecidableEq Symbol] (entry bodyEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (base step : Cache.Interned (EdgeKey Symbol Unit)) (depth ordinary : Value Symbol Unit)
    (state : State Symbol Unit) (facts : Facts state)
    (available : Available state (knot entry bodyEntry base step depth ordinary)) :
    ∃ result after,
      InternedFreshOrdinaryStoredSubstitution.unfold (knot entry bodyEntry base step depth ordinary) state = .done result after ∧
      InternedStoredSubstitution.unfold (knot entry bodyEntry base step depth ordinary) state = .done result after ∧
      Facts after ∧ Grows state after ∧ Cache.Extends state.nodes.issued after.nodes.issued ∧
      Available after result ∧ Available after (knot entry bodyEntry base step depth ordinary) ∧
      Exposed (knot entry bodyEntry base step depth ordinary) result base.key.symbol step.key.symbol := by
  let call := rebuild (knot entry bodyEntry base step depth ordinary) base.key.symbol step.key.symbol
  have checked := rebuild_checked (knot entry bodyEntry base step depth ordinary) base.key.symbol step.key.symbol state facts available
    (by simp [knot, Value.referenceOf])
  have growth := (InternedConstructorTemplates.run_correct call state facts.coherent.valid).2
  have history := run_issued_extends call state facts.coherent.valid
  exact ⟨(run call state).1, (run call state).2,
    current_unfold_work entry bodyEntry base step depth ordinary state,
    unfold_work entry bodyEntry base step depth ordinary state,
    checked.1, growth, history, checked.2.1, available.grows state _ growth history, checked.2.2⟩

end MicroCFTA.SourcePhysicalRecursiveRows
