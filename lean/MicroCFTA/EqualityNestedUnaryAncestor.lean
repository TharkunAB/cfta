import MicroCFTA.EqualityNestedUnaryWork

/-!
# Original unary occurrences through ancestor normalization

A unary ancestor can remove an empty child row or merge repeated complete
rows. Every nonempty original endpoint remains in the physical projection.
The nested endpoint worker also satisfies the existing source path-edit
reconstruction theorem with all original ancestor rows retained.
-/
namespace MicroCFTA.EqualityNestedUnaryAncestor
open SourceGuards FullSyntax InternedConstructorTemplates InternedRecordCoherence
open InternedProbeProvenance InternedNestedFacts InternedNestedProvenance InternedEdgeResidency
open EqualityNestedUnaryCarrier EqualityNestedUnaryChild EqualityNestedUnaryProduct EqualityMergedTargetReadback
open EqualityLeafProjectionPhysical EqualityLeafProjectionWorkers

noncomputable local instance : DecidableEq ConstraintKey := by classical exact inferInstance

/-- Read the sole child from each actual retained unary ancestor row. -/
def projected (value : Value Symbol Residual) : List (Value Symbol Residual) :=
  (nodeEdges value).flatMap EdgeValue.children

/-- Canonical ancestor rebuilding retains every nonempty original unary endpoint. -/
theorem projected_nonempty [DecidableEq (EdgeKey Symbol Residual)]
    (edges : List (EdgeValue Symbol Residual)) (state : State Symbol Residual)
    (coherent : Coherent state) (linked : Linked state) (resident : Edges state edges)
    (unary : ∀ edge ∈ edges, edge.children.length = 1)
    (child : Value Symbol Residual) (nonempty : child.referenceOf ≠ .empty) :
    child ∈ projected (run (makeNode edges) state).1 ↔ child ∈ edges.flatMap EdgeValue.children := by
  simp only [projected, makeNode_edges edges state coherent linked resident, List.mem_flatMap]
  constructor
  · rintro ⟨edge, member, found⟩
    exact ⟨edge, ((normalized_member state coherent edges resident edge).mp member).1, found⟩
  · rintro ⟨edge, member, found⟩
    have children : edge.children = [child] := by
      have length := unary edge member
      cases same : edge.children with
      | nil => simp only [same, List.not_mem_nil] at found
      | cons only rest =>
          have empty : rest = [] := by
            apply List.length_eq_zero_iff.mp
            simp only [same, List.length_cons] at length
            omega
          subst rest
          rw [same] at found
          exact congrArg List.singleton (List.mem_singleton.mp found).symm
    have live : dead edge = false := by
      simp only [dead, children, List.any_cons, List.any_nil, Bool.or_false, beq_eq_false_iff_ne]
      exact nonempty
    exact ⟨edge, (normalized_member state coherent edges resident edge).mpr ⟨member, live⟩, found⟩

/-- Each actual projected child comes from an original ancestor occurrence. -/
theorem projected_subset [DecidableEq (EdgeKey Symbol Residual)]
    (edges : List (EdgeValue Symbol Residual)) (state : State Symbol Residual)
    (coherent : Coherent state) (linked : Linked state) (resident : Edges state edges) :
    ∀ child ∈ projected (run (makeNode edges) state).1, child ∈ edges.flatMap EdgeValue.children := by
  intro child member
  obtain ⟨edge, included, found⟩ := List.mem_flatMap.mp member
  rw [makeNode_edges edges state coherent linked resident] at included
  exact List.mem_flatMap.mpr ⟨edge, ((normalized_member state coherent edges resident edge).mp included).1, found⟩

/-- Empty and repeated ancestor occurrences do not change the projected endpoint row union. -/
theorem projected_rows [DecidableEq (EdgeKey Symbol Residual)]
    (edges : List (EdgeValue Symbol Residual)) (before current : State Symbol Residual)
    (beforeCoherent : Coherent before) (beforeLinked : Linked before) (resident : Edges before edges)
    (unary : ∀ edge ∈ edges, edge.children.length = 1)
    (facts : Facts current) (available : Values current (edges.flatMap EdgeValue.children))
    (ordinary : ∀ child ∈ edges.flatMap EdgeValue.children, EqualityLeafProjectionUnion.OrdinaryRoot child)
    (live : ∀ child ∈ edges.flatMap EdgeValue.children, ∀ edge ∈ nodeEdges child, dead edge = false)
    (row : EdgeValue Symbol Residual) :
    row ∈ nodeEdges (run (makeUnion (projected (run (makeNode edges) before).1)) current).1 ↔
      ∃ child ∈ edges.flatMap EdgeValue.children, row ∈ nodeEdges child := by
  have subset := projected_subset edges before beforeCoherent beforeLinked resident
  rw [EqualityLeafProjectionUnion.union_edges _ current facts.coherent facts.linked
    (fun child member => (available child (subset child member)).resident)
    (fun child member => ordinary child (subset child member))
    (fun child member => live child (subset child member))]
  constructor
  · rintro ⟨child, member, found⟩
    exact ⟨child, subset child member, found⟩
  · rintro ⟨child, member, found⟩
    have nonempty : child.referenceOf ≠ .empty := by
      intro empty
      have same := (reference_empty child).mp empty
      simp only [same, nodeEdges, List.not_mem_nil] at found
    exact ⟨child, (projected_nonempty edges before beforeCoherent beforeLinked resident unary child nonempty).mpr member, found⟩

/-- Original finite indices determine the exact row predicate of the physical parent projection. -/
theorem projected_index_shape (parent leaf : Fin symbols) (rows : Fin count → Node initial)
    (values : EqualityNestedUnarySchedule.ValuesAt symbols count)
    (edges : List (EdgeValue (Fin symbols) ConstraintKey))
    (related : Language.All₂ (fun index edge => edge.children = [values index]) (List.finRange count) edges)
    (before current : State (Fin symbols) ConstraintKey)
    (beforeCoherent : Coherent before) (beforeLinked : Linked before) (resident : Edges before edges)
    (facts : Facts current) (represented : EqualityNestedUnarySchedule.Represents parent leaf current rows values) :
    NodeShape parent leaf (EqualityFixedProjectionInvariant.project rows)
      (run (makeUnion (projected (run (makeNode edges) before).1)) current).1 := by
  have origin : ∀ edge ∈ edges, ∃ index, edge.children = [values index] := by
    intro edge member
    obtain ⟨index, _, shape⟩ := EqualityMergedTargetShape.related_member _ _ _ related edge member
    exact ⟨index, shape⟩
  have childOrigin : ∀ child ∈ edges.flatMap EdgeValue.children, ∃ index, child = values index := by
    intro child member
    obtain ⟨edge, included, found⟩ := List.mem_flatMap.mp member
    obtain ⟨index, children⟩ := origin edge included
    exact ⟨index, by simpa only [children, List.mem_singleton] using found⟩
  have unary : ∀ edge ∈ edges, edge.children.length = 1 := by
    intro edge member
    obtain ⟨index, children⟩ := origin edge member
    simp only [children, List.length_singleton]
  have available : Values current (edges.flatMap EdgeValue.children) := by
    intro child member
    obtain ⟨index, rfl⟩ := childOrigin child member
    exact (represented index).1
  have ordinary : ∀ child ∈ edges.flatMap EdgeValue.children, EqualityLeafProjectionUnion.OrdinaryRoot child := by
    intro child member
    obtain ⟨index, rfl⟩ := childOrigin child member
    exact EqualityNestedUnaryUnion.normal_ordinary _ current facts (represented index).1 (represented index).2.1
  have live : ∀ child ∈ edges.flatMap EdgeValue.children, ∀ edge ∈ nodeEdges child, dead edge = false := by
    intro child member edge included
    obtain ⟨index, rfl⟩ := childOrigin child member
    obtain ⟨row, _, shape⟩ := (represented index).2.2.sound edge included
    exact row_live parent leaf row edge shape
  have exactRows := projected_rows edges before current beforeCoherent beforeLinked resident unary facts available ordinary live
  constructor
  · intro edge member
    obtain ⟨child, included, found⟩ := (exactRows edge).mp member
    obtain ⟨index, rfl⟩ := childOrigin child included
    obtain ⟨row, selected, shape⟩ := (represented index).2.2.sound edge found
    exact ⟨row, ⟨index, selected⟩, shape⟩
  · intro row selected
    obtain ⟨index, included⟩ := selected
    obtain ⟨edge, member, shape⟩ := (represented index).2.2.complete row included
    obtain ⟨ancestor, original, children⟩ := related_input _ _ _ related index (List.mem_finRange index)
    exact ⟨edge, (exactRows edge).mpr ⟨values index,
      List.mem_flatMap.mpr ⟨ancestor, original, by simp only [children, List.mem_singleton]⟩, member⟩, shape⟩

/-- The actual physical projection constructs the original indexed endpoint union in its runtime cache. -/
theorem projected_complete (parent leaf : Fin symbols) (rows : Fin count → Node initial)
    (values : EqualityNestedUnarySchedule.ValuesAt symbols count)
    (edges : List (EdgeValue (Fin symbols) ConstraintKey))
    (related : Language.All₂ (fun index edge => edge.children = [values index]) (List.finRange count) edges)
    (before current : State (Fin symbols) ConstraintKey)
    (beforeCoherent : Coherent before) (beforeLinked : Linked before) (resident : Edges before edges)
    (facts : Facts current) (prepared : MergedPhysicalWarmup.Prepared current)
    (represented : EqualityNestedUnarySchedule.Represents parent leaf current rows values) :
    MergedColdMerge.Complete (fun _ => MergedColdMerge.work
      (makeUnion (projected (run (makeNode edges) before).1))) current (fun after result =>
        Available after result ∧ Replayable result ∧ NodeShape parent leaf (EqualityFixedProjectionInvariant.project rows) result) := by
  let inputs := projected (run (makeNode edges) before).1
  have origin : ∀ child ∈ inputs, ∃ index, child = values index := by
    intro child member
    obtain ⟨edge, included, found⟩ := List.mem_flatMap.mp
      (projected_subset edges before beforeCoherent beforeLinked resident child member)
    obtain ⟨index, _, children⟩ := EqualityMergedTargetShape.related_member _ _ _ related edge included
    exact ⟨index, by simpa only [children, List.mem_singleton] using found⟩
  have available : Values current inputs := by
    intro child member
    obtain ⟨index, rfl⟩ := origin child member
    exact (represented index).1
  have replayable : ∀ child ∈ inputs, Replayable child := by
    intro child member
    obtain ⟨index, rfl⟩ := origin child member
    exact (represented index).2.1
  have normal : ∀ child ∈ inputs, EqualityOrdinaryReadback.Normal current child :=
    fun child member => replayable_normal child (replayable child member) current facts (available child member)
  have ordinary : ∀ child ∈ inputs, EqualityLeafProjectionUnion.OrdinaryRoot child :=
    fun child member => EqualityNestedUnaryUnion.normal_ordinary child current facts (available child member) (replayable child member)
  have verified := union_verified inputs current facts available
  let result := run (makeUnion inputs) current
  have resultAvailable : Available result.2 result.1 := verified.result _ _ rfl
  have readback := EqualityOrdinaryReadback.makeUnion_normal inputs current facts.coherent facts.linked
    (fun child member => (available child member).resident) ordinary normal
  apply MergedColdMergeSoundness.work_post _ current prepared Available _ verified
    (InternedShallowHeap.makeUnion_noNewMu inputs current)
  exact ⟨resultAvailable, ⟨result.2, verified.facts, resultAvailable, readback⟩,
    projected_index_shape parent leaf rows values edges related before current beforeCoherent beforeLinked resident facts represented⟩

/-- Replayable nullary child rows are inside the finite ordinary path fragment. -/
theorem leaf_ordinary (symbol : Fin symbols) (row : Row initial) (value : Value (Fin symbols) ConstraintKey)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state) (available : Available state value)
    (normal : Replayable value) (shape : LeafRow symbol row value) : Ordinary value := by
  have root := EqualityNestedUnaryUnion.normal_ordinary value state facts available normal
  have emptyChildren : ∀ edge ∈ nodeEdges value, edge.children = [] := by
    intro edge member
    have resident := resident_edges state facts.linked value available.resident edge member
    have fields := (facts.coherent.edges edge.entry.key edge resident).2.2
    have key := (shape edge.entry.key).mp ⟨edge, member, rfl⟩
    have empty : edge.children.map Value.referenceOf = [] := by
      rw [fields, key]
      rfl
    exact List.map_eq_nil_iff.mp empty
  cases value with
  | empty => trivial
  | reference | union | mu => contradiction
  | node entry edges depth free =>
      apply EqualityLeafProjectionParentStep.ordinary_edges
      intro edge member child found
      simp only [emptyChildren edge member, List.not_mem_nil] at found

/-- The concrete nested endpoint representation derives every path-worker fragment premise. -/
theorem endpoint_ordinary (parent leaf : Fin symbols) (rows : Node initial) (value : Value (Fin symbols) ConstraintKey)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state) (available : Available state value)
    (normal : Replayable value) (shape : NodeShape parent leaf rows value) : Ordinary value := by
  have root := EqualityNestedUnaryUnion.normal_ordinary value state facts available normal
  have childrenOrdinary : ∀ edge ∈ nodeEdges value, ∀ child ∈ edge.children, Ordinary child := by
    intro edge member child found
    obtain ⟨row, _, _, _, actual, children, childShape, childNormal⟩ := shape.sound edge member
    have same : child = actual := by simpa only [children, List.mem_singleton] using found
    subst child
    have resident := resident_edges state facts.linked value available.resident edge member
    exact leaf_ordinary leaf row actual state facts (facts.cached.edges edge.entry.key edge resident actual found)
      childNormal childShape
  cases value with
  | empty => trivial
  | reference | union | mu => contradiction
  | node entry edges depth free => exact EqualityLeafProjectionParentStep.ordinary_edges edges childrenOrdinary

/-- The selected endpoint branch is the exact nested intersection, including literal Empty. -/
theorem endpoint_edit (target value : Value (Fin symbols) ConstraintKey)
    (ordinary : EqualityLeafProjectionUnion.OrdinaryRoot value) (state : State (Fin symbols) ConstraintKey) :
    run (edit (fun target value => EqualityNestedUnaryWork.meet value target) [([], target)] value) state =
      (some (run (EqualityNestedUnaryWork.meet value target) state).1,
        (run (EqualityNestedUnaryWork.meet value target) state).2) := by
  cases value with
  | empty => simp only [edit_empty, run, EqualityNestedUnaryWork.meet_empty_left]
  | reference | union | mu => contradiction
  | node => simp [edit, EqualityLeafProjectionSyntax.atRoot, run_bind, run]

/-- Unary ancestor readback uses the same actual endpoint intersection at child index zero. -/
theorem unary_rebuild (target child : Value (Fin symbols) ConstraintKey)
    (edge : EdgeValue (Fin symbols) ConstraintKey) (children : edge.children = [child])
    (ordinary : EqualityLeafProjectionUnion.OrdinaryRoot child) (state : State (Fin symbols) ConstraintKey) :
    rebuild state (editedChild (fun target value => EqualityNestedUnaryWork.meet value target) [([0], target)] state) edge =
      (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint
        [(run (EqualityNestedUnaryWork.meet child target) state).1]) state).1 := by
  simp only [rebuild, children, EqualityLeafProjectionSyntax.mapChildren, editedChild, workerValue]
  have descend : EqualityLeafProjectionSyntax.descendEdits [([0], target)] 0 = [([], target)] := by
    simp [EqualityLeafProjectionSyntax.descendEdits]
  rw [descend, endpoint_edit target child ordinary state]
  rfl

/-- Actual nested endpoint edits satisfy reconstruction from all original ancestor occurrences. -/
theorem edit_original (first : EqualityLeafProjectionSyntax.Path × Value (Fin symbols) ConstraintKey)
    (rest : List (EqualityLeafProjectionSyntax.Path × Value (Fin symbols) ConstraintKey))
    (noRoot : EqualityLeafProjectionSyntax.atRoot (first :: rest) = none)
    (edges : List (EdgeValue (Fin symbols) ConstraintKey)) (before current : State (Fin symbols) ConstraintKey)
    (beforeCoherent : Coherent before) (linked : Linked before) (currentCoherent : Coherent current)
    (resident : Edges before edges)
    (ordinary : ∀ edge ∈ edges, ∀ child ∈ edge.children, Ordinary child) :
    let meet := fun target value => EqualityNestedUnaryWork.meet value target
    let request := fun index child => edit meet (EqualityLeafProjectionSyntax.descendEdits (first :: rest) index) child
    let result := run (edit meet (first :: rest) (run (makeNode edges) before).1) current
    let prepared := EqualityLeafProjectionParentCache.prepare request (fun _ => true) edges result.2
    result.1 = some (run (makeNode (edges.map (rebuild prepared (editedChild meet (first :: rest) prepared)))) prepared).1 :=
  EqualityLeafProjectionParentStep.edit_parent (fun target value => EqualityNestedUnaryWork.meet value target)
    (fun target value => EqualityNestedUnaryWork.meet_safe value target) first rest noRoot edges before current
    beforeCoherent linked currentCoherent resident ordinary

end MicroCFTA.EqualityNestedUnaryAncestor
