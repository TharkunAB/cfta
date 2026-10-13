import MicroCFTA.EqualityNestedUnaryAncestorRootSource
import MicroCFTA.EqualityLeafProjectionPathWorker

/-!
# Exact ordinary path workers at the two ancestor positions

The original stored requests derive the actual retained unary child rows.
The source getPath worker and edit worker then have the same complete run
as the projection and ancestor workers used by bounded root iteration.
-/
namespace MicroCFTA.EqualityNestedUnaryAncestorRoot
open SourceGuards FullSyntax InternedConstructorTemplates InternedRecordCoherence
open InternedProbeProvenance InternedNestedFacts InternedNestedProvenance InternedEdgeResidency
open MergedPhysicalWarmup MergedSourceComparison MergedColdMerge
open EqualityNestedUnaryCarrier EqualityNestedUnaryProduct EqualityNestedUnarySchedule EqualityMergedTargetReadback
open EqualityNestedUnaryAncestor EqualityNestedUnaryAncestorState
noncomputable local instance : DecidableEq ConstraintKey := by classical exact inferInstance

/-- Every retained physical ancestor row comes from one original endpoint index. -/
theorem stored_children (parent leaf : Fin symbols) (rows : Fin count → Node initial)
    (tags : Fin count → Fin symbols × ConstraintKey) (values : ValuesAt symbols count)
    (root : Value (Fin symbols) ConstraintKey) (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (stored : Stored tags values state root) (represented : Represents parent leaf state rows values) :
    ∀ edge ∈ nodeEdges root, ∃ index, edge.children = [values index] := by
  obtain ⟨edges, related, closed⟩ := stored
  have fields := stored_fields tags values state facts (fun index => (represented index).1) edges related
  have resident : Edges state edges := EnumerationSoundness.all₂_outputs _ _ _ (fields.imp (fun _ _ valid => valid.1))
  intro edge member
  have original : edge ∈ edges := by
    have found : edge ∈ nodeEdges (run (makeNode edges) state).1 := by simpa only [closed] using member
    rw [EqualityLeafProjectionPhysical.makeNode_edges edges state facts.coherent facts.linked resident] at found
    exact ((EqualityLeafProjectionPhysical.normalized_member state facts.coherent edges resident edge).mp found).1
  obtain ⟨index, _, valid⟩ := EqualityMergedTargetShape.related_member _ _ _ fields edge original
  exact ⟨index, valid.2.2.2⟩

/-- Reading child zero from each unary source row has no constructor effects. -/
theorem read_rows [DecidableEq (EdgeKey Symbol Payload)] (edges : List (EdgeValue Symbol Payload))
    (unary : ∀ edge ∈ edges, ∃ child, edge.children = [child]) (state : State Symbol Payload) :
    run (EqualityLeafProjectionPathWorker.rows (EqualityLeafProjectionPathWorker.read []) 0 edges) state =
      (some (edges.flatMap EdgeValue.children), state) := by
  induction edges with
  | nil => rfl
  | cons edge rest ih =>
    obtain ⟨child, children⟩ := unary edge List.mem_cons_self
    have tail := ih (fun edge member => unary edge (List.mem_cons_of_mem _ member))
    simp only [EqualityLeafProjectionPathWorker.read] at tail
    simp only [EqualityLeafProjectionPathWorker.rows, children, List.getElem?_cons_zero,
      EqualityLeafProjectionWorkers.bindOptional, EqualityLeafProjectionPathWorker.read, run_bind, run,
      tail, List.flatMap_cons, List.singleton_append]

/-- Actual ordinary getPath at child zero has the same exact projection result and cache. -/
theorem source_read_eq (parent leaf : Fin symbols) (rows : Fin count → Node initial)
    (tags : Fin count → Fin symbols × ConstraintKey) (values : ValuesAt symbols count)
    (root : Value (Fin symbols) ConstraintKey) (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (stored : Stored tags values state root) (represented : Represents parent leaf state rows values) :
    run (EqualityLeafProjectionPathWorker.read [0] root) state =
      (some (run (makeUnion (projected root)) state).1, (run (makeUnion (projected root)) state).2) := by
  have rootValid := stored_root tags values state facts (fun index => (represented index).1) root stored
  have ordinary := EqualityNestedUnaryUnion.normal_ordinary root state facts rootValid.1 rootValid.2
  have origin := stored_children parent leaf rows tags values root state facts stored represented
  have childOrigin : ∀ child ∈ projected root, ∃ index, child = values index := by
    intro child member
    obtain ⟨edge, present, included⟩ := List.mem_flatMap.mp member
    obtain ⟨index, children⟩ := origin edge present
    exact ⟨index, by simpa only [children, List.mem_singleton] using included⟩
  have childValid : ∀ child ∈ projected root, Available state child ∧ Replayable child := by
    intro child member
    obtain ⟨index, rfl⟩ := childOrigin child member
    exact ⟨(represented index).1, (represented index).2.1⟩
  have sourceUnion := EqualityOrdinaryUnionSource.union_run (projected root) state facts.coherent facts.linked
    (fun child member => (childValid child member).1.resident)
    (fun child member => EqualityNestedUnaryUnion.normal_ordinary child state facts
      (childValid child member).1 (childValid child member).2)
    (fun child member => replayable_normal child (childValid child member).2 state facts (childValid child member).1)
  cases root with
  | empty => simp [EqualityLeafProjectionPathWorker.read, projected, nodeEdges, makeUnion, distinctNodes, run]
  | reference | union | mu => contradiction
  | node entry edges depth free =>
    have read := read_rows edges (fun edge member => by obtain ⟨index, shape⟩ := origin edge member; exact ⟨values index, shape⟩) state
    simp only [EqualityLeafProjectionPathWorker.read] at read
    simp only [EqualityLeafProjectionPathWorker.read, EqualityLeafProjectionWorkers.bindOptional,
      run_bind, read, run]
    change (some (run (EqualityOrdinaryUnionSource.sourceUnion (projected (.node entry edges depth free))) state).1,
      (run (EqualityOrdinaryUnionSource.sourceUnion (projected (.node entry edges depth free))) state).2) = _
    rw [sourceUnion]

/-- Actual ordinary edit at child zero has the same exact result and cache as nodeWork. -/
theorem source_edit_eq (parent leaf : Fin symbols) (rows : Fin count → Node initial)
    (tags : Fin count → Fin symbols × ConstraintKey) (values : ValuesAt symbols count)
    (root target : Value (Fin symbols) ConstraintKey) (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (stored : Stored tags values state root) (represented : Represents parent leaf state rows values) :
    run (EqualityLeafProjectionWorkers.edit (fun target value => EqualityNestedUnaryWork.meet value target) [([0], target)] root) state =
      (some (run (EqualityNestedUnaryAncestorEdit.nodeWork target root) state).1,
        (run (EqualityNestedUnaryAncestorEdit.nodeWork target root) state).2) := by
  have rootValid := stored_root tags values state facts (fun index => (represented index).1) root stored
  apply EqualityNestedUnaryAncestorEdit.node_eq target root
    (EqualityNestedUnaryUnion.normal_ordinary root state facts rootValid.1 rootValid.2)
  intro edge member
  obtain ⟨index, children⟩ := stored_children parent leaf rows tags values root state facts stored represented edge member
  exact ⟨values index, children, EqualityNestedUnaryUnion.normal_ordinary _ state facts
    (represented index).1 (represented index).2.1⟩


/-- The root stop test is exactly equality of the ordered physical forest references. -/
theorem same_forest (first second : Roots symbols) : Same first second ↔
    ([first.1, first.2].map Value.referenceOf = [second.1, second.2].map Value.referenceOf) := by
  simp [Same]

/-- Execute the same two ancestor edits after both snapshot targets are available. -/
noncomputable def pairEditWork (first second : Value (Fin symbols) ConstraintKey) (roots : Roots symbols) :
    Work (Fin symbols) ConstraintKey (Roots symbols) :=
  (EqualityNestedUnaryAncestorEdit.nodeWork second roots.1).bind fun newLeft =>
    (EqualityNestedUnaryAncestorEdit.nodeWork first roots.2).bind fun newRight => .pure (newLeft, newRight)

/-- The two selected forest paths execute the same edits with the same final cache. -/
theorem source_forest_edit_eq (parent leaf : Fin symbols) (tags : Tags symbols left right)
    (rows : Projected initial left right) (roots : Roots symbols)
    (first second : Value (Fin symbols) ConstraintKey) (targetRows : Node initial)
    (secondShape : NodeShape parent leaf targetRows second) (secondNormal : Replayable second)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state) (prepared : Prepared state)
    (represented : RepresentsRoots parent leaf tags rows state roots) (secondAvailable : Available state second) :
    run (EqualityLeafProjectionWorkers.editChildren (fun target value => EqualityNestedUnaryWork.meet value target)
      [([0, 0], second), ([1, 0], first)] 0 [roots.1, roots.2]) state =
      (some [(run (pairEditWork first second roots) state).1.1, (run (pairEditWork first second roots) state).1.2],
        (run (pairEditWork first second roots) state).2) := by
  obtain ⟨values, leftStored, rightStored, leftValid, rightValid⟩ := represented
  obtain ⟨bound, output, after, done, extension, _⟩ := EqualityNestedUnaryAncestorEdit.edit_complete parent leaf rows.1
    tags.1 values.1 roots.1 second targetRows secondShape secondNormal state facts prepared leftStored leftValid secondAvailable
  have exactWork : run (EqualityNestedUnaryAncestorEdit.nodeWork second roots.1) state = (output, after) :=
    Prod.ext (Result.done.inj (done bound (Nat.le_refl _))).1 (Result.done.inj (done bound (Nat.le_refl _))).2
  have firstEdit := source_edit_eq parent leaf rows.1 tags.1 values.1 roots.1 second state facts leftStored leftValid
  have secondEdit := source_edit_eq parent leaf rows.2 tags.2 values.2 roots.2 first after extension.facts
    (stored_grows tags.2 values.2 state after facts.coherent.valid extension.growth roots.2 rightStored)
    (represents_grows parent leaf state after extension rows.2 values.2 rightValid)
  have zero : EqualityLeafProjectionSyntax.descendEdits [([0, 0], second), ([1, 0], first)] 0 = [([0], second)] := by
    simp [EqualityLeafProjectionSyntax.descendEdits]
  have one : EqualityLeafProjectionSyntax.descendEdits [([0, 0], second), ([1, 0], first)] 1 = [([0], first)] := by
    simp [EqualityLeafProjectionSyntax.descendEdits]
  simp only [EqualityLeafProjectionWorkers.editChildren, EqualityLeafProjectionWorkers.bindOptional,
    run_bind, zero, one, firstEdit, exactWork, secondEdit, pairEditWork, run]

end MicroCFTA.EqualityNestedUnaryAncestorRoot
