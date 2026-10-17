import MicroCFTA.SourceCurrentHereditaryConstructors

/-!
# Finite constraint depth above hereditary recursive values

Ordinary layers consume the finite bound. Stored unions keep that bound.
A hereditary value can occur at any depth, including depth zero. A Mu value
enters only through this hereditary case. Its ordinary unfolding can have
arbitrary height. This predicate alone does not restrict selected endpoints.
-/
namespace MicroCFTA.SourceCurrentConstrainedCap
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedRecordCoherence InternedFreshProbeKeys InternedNestedFacts
open SourceEqualityAnnotationLanguage
variable {Symbol Guard : Type}

/-- A finite ordinary prefix contains all guards that can fail the local predicate. -/
inductive Cap (valid : Guard → Prop) : Nat → Value Symbol Guard → Prop where
  | plain (depth : Nat) (annotated : Annotated valid value) : Cap valid depth value
  | node (depth : Nat) (entry) (edges : List (EdgeValue Symbol Guard)) (level free)
      (children : ∀ child ∈ edges.flatMap EdgeValue.children, Cap valid depth child) :
      Cap valid (depth + 1) (.node entry edges level free)
  | union (depth : Nat) (entry) (members : List (Value Symbol Guard)) (level free)
      (children : ∀ child ∈ members, Cap valid depth child) : Cap valid depth (.union entry members level free)

/-- At depth zero, every semantic guard satisfies the local predicate. -/
theorem Cap.annotated {valid : Guard → Prop} {depth : Nat} {value : Value Symbol Guard}
    (bounded : Cap valid depth value) (zero : depth = 0) : Annotated valid value := by
  induction bounded with
  | plain _ annotated => exact annotated
  | node => omega
  | union depth entry members level free children ih =>
      exact .union entry members level free (fun child member => ih child member zero)

/-- A zero bound is exactly the existing hereditary annotation contract. -/
theorem zero_iff (valid : Guard → Prop) (value : Value Symbol Guard) :
    Cap valid 0 value ↔ Annotated valid value := ⟨fun bounded => bounded.annotated rfl, Cap.plain 0⟩

/-- A larger bound retains the same supplied semantic value. -/
theorem Cap.mono {valid : Guard → Prop} {depth : Nat} {value : Value Symbol Guard}
    (bounded : Cap valid depth value) {larger : Nat} (increase : depth ≤ larger) : Cap valid larger value := by
  induction bounded generalizing larger with
  | plain _ annotated => exact .plain larger annotated
  | node depth entry edges level free children ih =>
      cases larger with
      | zero => omega
      | succ larger => exact .node larger entry edges level free (fun child member => ih child member (by omega))
  | union depth entry members level free children ih =>
      exact .union larger entry members level free (fun child member => ih child member increase)

/-- A row at zero is hereditary; a positive row consumes one ordinary layer. -/
def Edge (valid : Guard → Prop) (depth : Nat) (edge : EdgeValue Symbol Guard) : Prop :=
  match depth with
  | 0 => SourceCurrentHereditaryConstructors.Edge valid edge
  | depth + 1 => ∀ child ∈ edge.children, Cap valid depth child

/-- Each complete ordinary row retains the bound of its supplied parent value. -/
theorem node_edge {valid : Guard → Prop} {depth : Nat} {value : Value Symbol Guard}
    (bounded : Cap valid depth value) (edge : EdgeValue Symbol Guard) (member : edge ∈ nodeEdges value) : Edge valid depth edge := by
  cases bounded with
  | plain depth annotated =>
      have row := SourceCurrentHereditaryConstructors.node_edge annotated edge member
      cases depth with
      | zero => exact row
      | succ depth => exact fun child present => .plain depth (row.2 child present)
  | node depth entry edges level free children =>
      exact fun child present => children child (List.mem_flatMap.mpr ⟨edge, member, present⟩)
  | union => cases member

/-- A positive ordinary parent gives a strictly smaller constraint-depth bound for each child. -/
theorem node_child {valid : Guard → Prop} {depth : Nat} {entry edges level free}
    (bounded : Cap valid (depth + 1) (.node entry edges level free))
    (edge : EdgeValue Symbol Guard) (member : edge ∈ edges) (child : Value Symbol Guard) (present : child ∈ edge.children) :
    Cap valid depth child := node_edge bounded edge member child present

/-- A larger row bound retains all original children. -/
theorem edge_mono {valid : Guard → Prop} {depth larger : Nat} {edge : EdgeValue Symbol Guard}
    (bounded : Edge valid depth edge) (increase : depth ≤ larger) : Edge valid larger edge := by
  cases larger with
  | zero =>
      have same : depth = 0 := by omega
      subst depth
      exact bounded
  | succ larger =>
      cases depth with
      | zero => exact fun child member => .plain larger (bounded.2 child member)
      | succ depth => exact fun child member => (bounded child member).mono (by omega)

/-- Complete supplied rows determine the same ordinary parent bound. -/
theorem ordinary (valid : Guard → Prop) (depth : Nat) (entry) (edges : List (EdgeValue Symbol Guard)) (level free)
    (rows : ∀ edge ∈ edges, Edge valid depth edge) : Cap valid depth (.node entry edges level free) := by
  cases depth with
  | zero =>
      apply Cap.plain 0
      exact .node entry edges level free (fun edge member => (rows edge member).1)
        (fun child member => by
          obtain ⟨edge, present, inside⟩ := List.mem_flatMap.mp member
          exact (rows edge present).2 child inside)
  | succ depth =>
      apply Cap.node depth
      intro child member
      obtain ⟨edge, present, inside⟩ := List.mem_flatMap.mp member
      exact rows edge present child inside

/-- Literal edge work retains the exact guard and child constraint bounds. -/
theorem makeEdge [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (depth : Nat)
    (symbol : Symbol) (guard : Guard) (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (cached : Cached state)
    (available : ∀ value ∈ values, Available state value) (guardValid : depth = 0 → valid guard)
    (bounded : ∀ child ∈ values, Cap valid (depth - 1) child) :
    Edge valid depth (run (InternedConstructorTemplates.makeEdge symbol guard values) state).1 := by
  cases result : (run (InternedConstructorTemplates.makeEdge symbol guard values) state).1 with
  | mk entry children =>
      have key := InternedOrdinaryAbsenceReplay.makeEdge_key symbol guard values state coherent
      have exactChildren := InternedShallowValues.makeEdge_children symbol guard values state coherent cached available
      rw [result] at key exactChildren
      change entry.key = _ at key
      change children = values at exactChildren
      cases depth with
      | zero =>
          change valid entry.key.constraint ∧ ∀ child ∈ children, Annotated valid child
          rw [key, exactChildren]
          exact ⟨guardValid rfl, fun child member => (bounded child member).annotated rfl⟩
      | succ depth =>
          change ∀ child ∈ children, Cap valid depth child
          rw [exactChildren]
          exact bounded

/-- Canonical node readback retains the finite bound of the actual supplied rows. -/
theorem makeNode [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (depth : Nat)
    (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) (linked : Linked state)
    (resident : ∀ edge ∈ edges, EdgeResident state edge) (bounded : ∀ edge ∈ edges, Edge valid depth edge) :
    Cap valid depth (run (InternedConstructorTemplates.makeNode edges) state).1 := by
  have selected : ∀ edge ∈ canonicalEdges (surviving edges), EdgeResident state edge :=
    fun edge member => resident edge (List.mem_filter.mp (canonicalEdges_member _ edge member)).1
  have rows : ∀ edge ∈ canonicalEdges (surviving edges), Edge valid depth edge :=
    fun edge member => bounded edge (List.mem_filter.mp (canonicalEdges_member _ edge member)).1
  unfold InternedConstructorTemplates.makeNode
  dsimp only
  split
  · exact .plain depth .empty
  · rename_i first rest same
    obtain ⟨entry, exactResult⟩ := identifyNode_readback (first :: rest) state coherent linked
      (by simpa only [same] using selected)
    simp only [run, exactResult, identifyNode]
    exact ordinary valid depth entry _ _ _ (by simpa only [same] using rows)

/-- Flattened union members retain their original finite constraint bound. -/
theorem union_member {valid : Guard → Prop} {depth : Nat} {value : Value Symbol Guard}
    (bounded : Cap valid depth value) (member : Value Symbol Guard) (present : member ∈ unionMembers value) : Cap valid depth member := by
  cases bounded with
  | plain depth annotated => exact .plain depth (SourceCurrentHereditaryConstructors.union_member valid value annotated member present)
  | node depth entry edges level free children => exact (List.mem_singleton.mp present) ▸ Cap.node depth entry edges level free children
  | union depth entry members level free children => exact children member present

private theorem ordinary_rows (valid : Guard → Prop) (depth : Nat) (values : List (Value Symbol Guard))
    (edges : List (EdgeValue Symbol Guard)) (bounded : ∀ value ∈ values, Cap valid depth value)
    (found : ordinaryEdges values = some edges) : ∀ edge ∈ edges, Edge valid depth edge := by
  induction values generalizing edges with
  | nil => cases Option.some.inj found; intro edge member; cases member
  | cons value rest ih =>
      cases value <;> simp only [ordinaryEdges] at found
      case node entry rows level free =>
        cases tail : ordinaryEdges rest with
        | none => simp only [tail, Option.map_none] at found; cases found
        | some later =>
            have same := Option.some.inj (by simpa only [tail, Option.map_some] using found)
            subst edges
            intro edge member
            rcases List.mem_append.mp member with first | last
            · exact node_edge (bounded _ List.mem_cons_self) edge first
            · exact ih later (fun value member => bounded value (List.mem_cons_of_mem _ member)) tail edge last
      all_goals cases found

/-- Actual union normalization retains finite constraint depth across every source branch. -/
theorem makeUnion [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (depth : Nat)
    (values : List (Value Symbol Guard)) (state : State Symbol Guard) (facts : Facts state)
    (available : ∀ value ∈ values, Available state value) (bounded : ∀ value ∈ values, Cap valid depth value) :
    Cap valid depth (run (InternedConstructorTemplates.makeUnion values) state).1 := by
  have selected : ∀ value ∈ distinctNodes (values.flatMap unionMembers), Cap valid depth value := by
    intro value member
    obtain ⟨original, present, inside⟩ := List.mem_flatMap.mp (distinctNodes_member _ value member)
    exact union_member (bounded original present) value inside
  cases normalized : distinctNodes (values.flatMap unionMembers) with
  | nil => simpa only [InternedConstructorTemplates.makeUnion, normalized, run] using (Cap.plain depth (Annotated.empty (valid := valid)))
  | cons first rest =>
      cases rest with
      | nil => simpa only [InternedConstructorTemplates.makeUnion, normalized, run] using selected first (by simp [normalized])
      | cons second tail =>
          have inputs : ∀ value ∈ first :: second :: tail, Available state value := by
            simpa only [InternedNestedProvenance.Values, normalized] using InternedUnionFilterFusion.selected_available values state available
          have safe : ∀ value ∈ first :: second :: tail, Cap valid depth value := by simpa only [normalized] using selected
          cases ordinary : ordinaryEdges (first :: second :: tail) with
          | some edges =>
              have resident := ordinaryEdges_resident _ edges state facts.linked (fun value member => (inputs value member).resident) ordinary
              simpa only [InternedConstructorTemplates.makeUnion, normalized, ordinary] using makeNode valid depth edges state facts.coherent facts.linked resident
                (ordinary_rows valid depth _ edges safe ordinary)
          | none =>
              obtain ⟨entry, returned⟩ := InternedUnionFilterFusion.union_readback values first second tail state facts available normalized ordinary
              rw [returned]
              exact .union depth entry _ _ _ safe

end MicroCFTA.SourceCurrentConstrainedCap
