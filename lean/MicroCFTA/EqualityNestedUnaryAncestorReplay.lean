import MicroCFTA.EqualityNestedUnaryAncestorCompile
import MicroCFTA.EqualityLeafProjectionEditClosed

/-!
# Original unary ancestor replay in the actual edit cache

Completed source edits retain each selected child and rebuilt edge request.
Live original rows occur in the canonical source rows. Dead unary rows have
an empty child, so their complete edge key remains unchanged. The actual
returned cache therefore suffices for original-occurrence reconstruction.
-/
namespace MicroCFTA.EqualityNestedUnaryAncestorReplay
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance InternedEdgeResidency
open EqualityLeafProjectionSyntax (Path descendEdits mapChildren)
open EqualityLeafProjectionWorkers EqualityLeafProjectionPhysical
open EqualityLeafProjectionClosedWorkers

/-- A successful closed child list contains each closed original position request. -/
theorem child_closed [DecidableEq (EdgeKey Symbol Guard)]
    (meet : Target → Value Symbol Guard → Work Symbol Guard (Value Symbol Guard))
    (edits : List (Path × Target)) (offset : Nat) (children : List (Value Symbol Guard))
    (state : State Symbol Guard) (valid : Valid state) (values : List (Value Symbol Guard))
    (closed : run (editChildren meet edits offset children) state = (some values, state))
    (index : Nat) (child : Value Symbol Guard) (member : (index, child) ∈ indexed offset children) :
    run (edit meet (descendEdits edits index) child) state =
      (some (editedChild meet edits state index child), state) := by
  induction children generalizing offset values with
  | nil => simp [indexed] at member
  | cons first rest ih =>
      obtain ⟨value, tail, _, headClosed, tailClosed⟩ :=
        EqualityLeafProjectionEditClosed.children_decompose meet edits offset first rest state valid values closed
      rcases List.mem_cons.mp member with same | later
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
        simp only [editedChild, workerValue, headClosed, Option.getD_some]
      · exact ih (offset + 1) tail tailClosed later

/-- A successful closed source row list retains each rebuilt original row request. -/
theorem edge_closed [DecidableEq (EdgeKey Symbol Guard)]
    (meet : Target → Value Symbol Guard → Work Symbol Guard (Value Symbol Guard))
    (edits : List (Path × Target)) (edges : List (EdgeValue Symbol Guard)) (ordinary : OrdinaryEdges edges)
    (state : State Symbol Guard) (valid : Valid state) (values : List (EdgeValue Symbol Guard))
    (closed : run (editEdges meet edits edges) state = (some values, state))
    (edge : EdgeValue Symbol Guard) (member : edge ∈ edges) :
    run (rebuildWork (editedChild meet edits state) edge) state =
      (rebuild state (editedChild meet edits state) edge, state) ∧
    ∀ index child, (index, child) ∈ indexed 0 edge.children →
      run (edit meet (descendEdits edits index) child) state =
        (some (editedChild meet edits state index child), state) := by
  induction edges generalizing values with
  | nil => contradiction
  | cons first rest ih =>
      cases first with
      | mk entry children =>
          obtain ⟨nodes, result, tail, _, childClosed, edgeClosed, tailClosed⟩ :=
            EqualityLeafProjectionEditClosed.edges_decompose meet edits entry children rest state valid values closed
          rcases List.mem_cons.mp member with rfl | later
          · have readback := EqualityLeafProjectionWorkerReadback.editChildren_readback meet edits 0 children ordinary.1
              state state valid (by rw [childClosed]; exact grows_refl state)
            have same : nodes = mapChildren (editedChild meet edits state) 0 children :=
              Option.some.inj ((congrArg Prod.fst childClosed).symm.trans readback)
            rw [same] at edgeClosed
            refine ⟨?_, fun index child member => child_closed meet edits 0 children state valid nodes childClosed index child member⟩
            change run (makeEdge entry.key.symbol entry.key.constraint (mapChildren (editedChild meet edits state) 0 children)) state =
              ((run (makeEdge entry.key.symbol entry.key.constraint (mapChildren (editedChild meet edits state) 0 children)) state).1, state)
            rw [edgeClosed]
          · exact ih ordinary.2 tail tailClosed later

/-- A dead unary row has exactly one literal empty child. -/
theorem unary_dead (edge : EdgeValue Symbol Guard) (unary : edge.children.length = 1) (dead : dead edge = true) :
    edge.children = [.empty] := by
  cases children : edge.children with
  | nil => simp only [children, List.length_nil] at unary; omega
  | cons child rest =>
      have empty : rest = [] := by
        apply List.length_eq_zero_iff.mp
        simp only [children, List.length_cons] at unary
        omega
      subst rest
      have ref : child.referenceOf = .empty := by
        simpa only [EqualityLeafProjectionPhysical.dead, children, List.any_cons, List.any_nil,
          Bool.or_false, beq_iff_eq] using dead
      have same := (reference_empty child).mp ref
      simp only [same]

/-- An already dead unary occurrence reuses its old complete edge in the returned cache. -/
theorem dead_rebuild [DecidableEq (EdgeKey Symbol Guard)]
    (meet : Target → Value Symbol Guard → Work Symbol Guard (Value Symbol Guard)) (edits : List (Path × Target))
    (edge : EdgeValue Symbol Guard) (unary : edge.children.length = 1) (dead : dead edge = true)
    (state : State Symbol Guard) (coherent : Coherent state) (resident : EdgeResident state edge) :
    run (rebuildWork (editedChild meet edits state) edge) state = (edge, state) := by
  have children := unary_dead edge unary dead
  have same : mapChildren (editedChild meet edits state) 0 edge.children = edge.children := by
    simp only [children, mapChildren, editedChild_empty]
  unfold rebuildWork
  rw [same]
  exact EqualityLeafProjectionNullaryEdit.resident_edge_replay edge state coherent resident

/-- A completed ordinary parent retains all actual row requests and its final constructor. -/
theorem parent_closed [DecidableEq (EdgeKey Symbol Guard)]
    (meet : Target → Value Symbol Guard → Work Symbol Guard (Value Symbol Guard))
    (first : Path × Target) (rest : List (Path × Target))
    (noRoot : EqualityLeafProjectionSyntax.atRoot (first :: rest) = none)
    (value output : Value Symbol Guard) (ordinary : Ordinary value)
    (state : State Symbol Guard) (valid : Valid state)
    (closed : run (edit meet (first :: rest) value) state = (some output, state)) :
    run (makeNode ((nodeEdges value).map (rebuild state (editedChild meet (first :: rest) state)))) state = (output, state) ∧
    ∀ edge ∈ nodeEdges value,
      run (rebuildWork (editedChild meet (first :: rest) state) edge) state =
        (rebuild state (editedChild meet (first :: rest) state) edge, state) ∧
      ∀ index child, (index, child) ∈ indexed 0 edge.children →
        run (edit meet (descendEdits (first :: rest) index) child) state =
          (some (editedChild meet (first :: rest) state index child), state) := by
  cases value with
  | empty =>
      have same : output = .empty := (Option.some.inj (congrArg Prod.fst closed)).symm
      subst output
      constructor
      · simp [nodeEdges, makeNode, canonicalEdges, surviving, EnumerationBuilderCaches.canonicalIds, run]
      · simp only [nodeEdges, List.not_mem_nil, false_implies, implies_true]
  | reference | union | mu => contradiction
  | node entry edges depth free =>
      have requests := closed
      rw [edit, noRoot] at requests
      obtain ⟨rows, rowClosed, _⟩ := optional_bind_closed _ _ state valid output requests
      exact ⟨EqualityLeafProjectionEditClosed.parent_replay meet first rest entry edges depth free ordinary noRoot
        state state valid output (congrArg Prod.fst closed) (by rw [closed]; exact grows_refl state),
        fun edge member => edge_closed meet (first :: rest) edges ordinary state valid rows rowClosed edge member⟩

/-- The actual edit cache reconstructs every original unary occurrence without preparation. -/
theorem actual_original [DecidableEq (EdgeKey Symbol Guard)]
    (meet : Target → Value Symbol Guard → Work Symbol Guard (Value Symbol Guard))
    (meetSafe : ∀ target value, Safe (meet target value))
    (first : Path × Target) (rest : List (Path × Target))
    (noRoot : EqualityLeafProjectionSyntax.atRoot (first :: rest) = none)
    (edges : List (EdgeValue Symbol Guard)) (before current : State Symbol Guard)
    (beforeCoherent : Coherent before) (linked : Linked before) (currentCoherent : Coherent current)
    (growth : Grows before current) (resident : ∀ edge ∈ edges, EdgeResident before edge)
    (unary : ∀ edge ∈ edges, edge.children.length = 1)
    (ordinary : ∀ edge ∈ edges, ∀ child ∈ edge.children, Ordinary child) :
    let actual := run (edit meet (first :: rest) (run (makeNode edges) before).1) current
    ∃ output, actual.1 = some output ∧
      run (makeNode (edges.map (rebuild actual.2 (editedChild meet (first :: rest) actual.2)))) actual.2 = (output, actual.2) ∧
      ∀ edge ∈ edges,
        run (rebuildWork (editedChild meet (first :: rest) actual.2) edge) actual.2 =
          (rebuild actual.2 (editedChild meet (first :: rest) actual.2) edge, actual.2) ∧
        ∀ index child, (index, child) ∈ indexed 0 edge.children →
          run (edit meet (descendEdits (first :: rest) index) child) actual.2 =
            (some (editedChild meet (first :: rest) actual.2 index child), actual.2) := by
  let root := (run (makeNode edges) before).1
  let actual := run (edit meet (first :: rest) root) current
  have rootOrdinary : Ordinary root := by
    have rootKind := EqualityLeafProjectionUnion.makeNode_ordinary edges before beforeCoherent linked resident
    have rowsOrdinary := EqualityLeafProjectionParentStep.normalized_ordinary edges before beforeCoherent linked resident ordinary
    change EqualityLeafProjectionUnion.OrdinaryRoot root at rootKind
    change OrdinaryEdges (nodeEdges root) at rowsOrdinary
    cases same : root with
    | empty => trivial
    | reference | union | mu => simp only [same, EqualityLeafProjectionUnion.OrdinaryRoot] at rootKind
    | node entry rows depth free => simpa only [same, nodeEdges, EqualityLeafProjectionWorkers.Ordinary] using rowsOrdinary
  obtain ⟨output, returned⟩ := edit_returns meet (first :: rest) root rootOrdinary current
  have afterCoherent : Coherent actual.2 := edit_coherent meet meetSafe (first :: rest) root current currentCoherent
  have afterGrowth : Grows before actual.2 := grows_trans growth
    (InternedConstructorTemplates.run_correct _ current currentCoherent.valid).2
  have closed : run (edit meet (first :: rest) root) actual.2 = (some output, actual.2) := by
    simpa only [returned] using replay (edit meet (first :: rest) root) current actual.2 currentCoherent.valid (grows_refl _)
  have canonical := parent_closed meet first rest noRoot root output rootOrdinary actual.2 afterCoherent.valid closed
  have original : ∀ edge ∈ edges,
      run (rebuildWork (editedChild meet (first :: rest) actual.2) edge) actual.2 =
        (rebuild actual.2 (editedChild meet (first :: rest) actual.2) edge, actual.2) ∧
      ∀ index child, (index, child) ∈ indexed 0 edge.children →
        run (edit meet (descendEdits (first :: rest) index) child) actual.2 =
          (some (editedChild meet (first :: rest) actual.2 index child), actual.2) := by
    intro edge member
    cases deadness : dead edge with
    | false =>
        have selected : edge ∈ nodeEdges root := by
          rw [makeNode_edges edges before beforeCoherent linked resident]
          exact (normalized_member before beforeCoherent edges resident edge).mpr ⟨member, deadness⟩
        exact canonical.2 edge selected
    | true =>
        have repeated := dead_rebuild meet (first :: rest) edge (unary edge member) deadness actual.2 afterCoherent
          (edge_grows before actual.2 afterGrowth edge (resident edge member))
        have same : rebuild actual.2 (editedChild meet (first :: rest) actual.2) edge = edge := congrArg Prod.fst repeated
        refine ⟨by rw [same]; exact repeated, ?_⟩
        intro index child position
        have childEmpty : child = .empty := by
          simpa only [unary_dead edge (unary edge member) deadness, List.mem_singleton] using indexed_member 0 index edge.children child position
        subst child
        simp only [edit_empty, editedChild_empty, run]
  have changedResident : ∀ edge ∈ edges, EdgeResident actual.2 (rebuild actual.2 (editedChild meet (first :: rest) actual.2) edge) := by
    intro edge member
    have found := makeEdge_resident edge.entry.key.symbol edge.entry.key.constraint
      (mapChildren (editedChild meet (first :: rest) actual.2) 0 edge.children) actual.2 afterCoherent
    have repeated := (original edge member).1
    change run (makeEdge edge.entry.key.symbol edge.entry.key.constraint
      (mapChildren (editedChild meet (first :: rest) actual.2) 0 edge.children)) actual.2 = _ at repeated
    rw [repeated] at found
    exact found
  have normalized := rebuild_readback before actual.2 actual.2 beforeCoherent linked afterCoherent afterCoherent
    edges resident (fun _ => true) (editedChild meet (first :: rest) actual.2)
    (editedChild_empty meet (first :: rest) actual.2) changedResident
  have keep (rows : List (EdgeValue Symbol Guard)) : rows.filter (fun _ => true) = rows :=
    List.filter_eq_self.mpr (fun _ _ => rfl)
  simp only [keep] at normalized
  exact ⟨output, returned, by rw [normalized]; exact canonical.1, original⟩

end MicroCFTA.EqualityNestedUnaryAncestorReplay
