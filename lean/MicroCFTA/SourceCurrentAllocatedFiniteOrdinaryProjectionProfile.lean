import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryProjection
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOutputConstructors

/-!
# Profiles and height bounds for actual ordinary projections

Each ordinary projection unions at most one result per source row.
The row envelope counts these concatenated source occurrences.
Forest root union retains its separate operand count.
Every bound belongs to the same supplied graph and returned record.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryProjectionProfile
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceEqualityProjectionRead SourceEqualityProjectionUnion SourceEqualityProjectionGraph
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile
open MergedOrdinaryHeight (height edgeHeight edgesHeight childrenHeight)
variable {Symbol Guard : Type}

/-- Bound the rows at every ordinary descendant after a finite path. -/
def projectRows (rows depth : Nat) : Nat := (max 1 rows) ^ (depth + 1)

/-- Include the separate forest root union in the common path envelope. -/
def forestRows (rows count depth : Nat) : Nat := max 1 count * projectRows rows depth

/-- The empty node path retains its original row profile. -/
theorem projectRows_base (rows : Nat) : rows ≤ projectRows rows 0 := by
  simpa only [projectRows, Nat.zero_add, Nat.pow_one] using Nat.le_max_right 1 rows

/-- One source projection level multiplies by the uniform source row limit. -/
theorem projectRows_step (rows depth : Nat) :
    projectRows rows (depth + 1) = max 1 rows * projectRows rows depth := by
  simp only [projectRows, Nat.pow_succ, Nat.mul_comm]

/-- A longer path permits the same output row envelope. -/
theorem projectRows_mono (rows : Nat) {first last : Nat} (bound : first ≤ last) :
    projectRows rows first ≤ projectRows rows last := by
  induction bound with
  | refl => exact Nat.le_refl _
  | @step last _ ih =>
      apply Nat.le_trans ih
      rw [projectRows_step]
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right (projectRows rows last) (Nat.le_max_left 1 rows)

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Finite ordinary reads expose exactly the stored source rows without changing the heap. -/
theorem read_exact {value : Value Symbol Guard} {before after : State Symbol Guard}
    {edges : List (EdgeValue Symbol Guard)} (actual : Read value before edges after)
    (domain : SourceCurrentAllocatedFiniteOrdinaryDomain.Node value) :
    edges = nodeEdges value ∧ after = before := by
  cases actual with
  | done fuel completed =>
      cases domain with
      | empty =>
          simp only [MergedFreshOrdinaryExposure.nodeEdges] at completed
          cases completed
          exact ⟨rfl, rfl⟩
      | ordinary rows =>
          simp only [MergedFreshOrdinaryExposure.nodeEdges] at completed
          cases completed
          exact ⟨rfl, rfl⟩

/-- Ordered ordinary reads concatenate the literal rows at the unchanged source heap. -/
theorem readAll_exact {values : List (Value Symbol Guard)} {before after : State Symbol Guard}
    {edges : List (EdgeValue Symbol Guard)} (actual : ReadAll values before edges after)
    (domain : SourceCurrentAllocatedFiniteOrdinaryDomain.Children values) :
    edges = values.flatMap nodeEdges ∧ after = before := by
  induction actual with
  | nil => exact ⟨rfl, rfl⟩
  | cons first rest ih =>
      cases domain with
      | cons firstDomain restDomain =>
          have one := read_exact first firstDomain
          have later := ih restDomain
          exact ⟨by simp only [List.flatMap_cons, one.1, later.1], later.2.trans one.2⟩

omit [DecidableEq (EdgeKey Symbol Guard)] in
private theorem flattened_rows {rows arity : Nat} (values : List (Value Symbol Guard))
    (profile : ChildrenShape rows arity values) :
    RowsShape rows arity (values.flatMap nodeEdges) ∧
      (values.flatMap nodeEdges).length ≤ values.length * rows := by
  constructor
  · apply SourceCurrentAllocatedFiniteOrdinaryOutputConstructors.rows_of_members
    intro edge member
    obtain ⟨value, present, included⟩ := List.mem_flatMap.mp member
    exact RowsShape.member _ (NodeShape.nodeEdges value (ChildrenShape.member values profile value present)) edge included
  · induction values with
    | nil => simp
    | cons value rest ih =>
        have first := NodeShape.length value profile.1
        have later := ih profile.2
        simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
        omega

/-- Source union derives a profile from its actual concatenated row count and retains maximum height. -/
theorem union {rows arity : Nat} {values : List (Value Symbol Guard)} {before after : State Symbol Guard}
    {result : Value Symbol Guard} (actual : Union values before result after)
    (semantic : SemanticReady before) (available : Values before values)
    (profile : ChildrenShape rows arity values) :
    NodeShape (max 1 values.length * rows) arity result ∧ height result ≤ childrenHeight values := by
  cases actual with
  | node read built =>
      obtain ⟨sameRows, sameHeap⟩ := readAll_exact read (ChildrenShape.domain values profile)
      rw [sameRows, sameHeap] at built
      have facts := semantic.ready.semantic.1.normal.facts
      have resident : ∀ edge ∈ values.flatMap nodeEdges, EdgeResident before edge := by
        intro edge member
        obtain ⟨value, present, included⟩ := List.mem_flatMap.mp member
        exact resident_edges before facts.linked value (available value present).resident edge included
      have collected := flattened_rows values profile
      have increased : rows ≤ max 1 values.length * rows := by
        simpa only [Nat.one_mul] using Nat.mul_le_mul_right rows (Nat.le_max_left 1 values.length)
      have shaped := SourceCurrentAllocatedFiniteOrdinaryOutputConstructors.makeNode _ before facts.coherent facts.linked
        resident (RowsShape.mono _ collected.1 increased (Nat.le_refl _))
        (Nat.le_trans collected.2 (Nat.mul_le_mul_right rows (Nat.le_max_right 1 values.length)))
      have bounded := MergedOrdinaryHeight.ordinaryUnion_bound values before facts.coherent facts.linked
        (fun value member => (available value member).resident) (childrenHeight values)
        ((MergedOrdinaryHeight.childrenHeight_le _ _).mp (Nat.le_refl _))
      simpa only [MergedOrdinaryHeight.ordinaryUnion, built] using And.intro shaped bounded

private def NodeResult (path : List Int) (input : Value Symbol Guard) (before : State Symbol Guard)
    (result : Value Symbol Guard) (_after : State Symbol Guard) : Prop :=
  ∀ rows arity, SemanticReady before → Available before input → NodeShape rows arity input →
    NodeShape (projectRows rows path.length) arity result ∧ height result ≤ height input

private def RowsResult (path : List Int) (edges : List (EdgeValue Symbol Guard)) (before : State Symbol Guard)
    (results : List (Value Symbol Guard)) (_after : State Symbol Guard) : Prop :=
  ∀ rows arity, SemanticReady before → Edges before edges → RowsShape rows arity edges →
    ChildrenShape (projectRows rows path.length) arity results ∧ results.length ≤ edges.length ∧
      childrenHeight results ≤ edgesHeight edges

private theorem projection :
    (∀ path (value : Value Symbol Guard) before result after,
      Project path value before result after → NodeResult path value before result after) ∧
    (∀ path index (edges : List (EdgeValue Symbol Guard)) before results after,
      ProjectRows path index edges before results after → RowsResult path edges before results after) := by
  have rootCase : ∀ {value : Value Symbol Guard} {state}, NodeResult [] value state value state := by
    intro value state rows arity _ _ profile
    exact ⟨NodeShape.mono value profile (projectRows_base rows) (Nat.le_refl _), Nat.le_refl _⟩
  have emptyCase : ∀ {index path state}, NodeResult (index :: path) (.empty : Value Symbol Guard) state .empty state := by
    intro index path state rows arity _ _ _
    exact ⟨True.intro, Nat.le_refl _⟩
  have ordinaryCase : ∀ {path index edges before values middle result after entry depth free},
      ProjectRows (Symbol := Symbol) (Guard := Guard) path index edges before values middle →
      Union values middle result after → RowsResult path edges before values middle →
      NodeResult (index :: path) (.node entry edges depth free) before result after := by
    intro path index edges before values middle result after entry depth free actual unionTrace ih rows arity semantic available profile
    have resident := resident_edges before semantic.ready.semantic.1.normal.facts.linked _ available.resident
    have outputs := ih rows arity semantic resident profile.2
    have physical := SourceCurrentAllocatedFiniteOrdinaryProjection.rows actual semantic resident (RowsShape.domain edges profile.2)
    have merged := union unionTrace physical.2.1 physical.2.2.1 outputs.1
    have count : max 1 values.length ≤ max 1 rows := Nat.max_le.mpr ⟨Nat.le_max_left _ _,
      Nat.le_trans outputs.2.1 (Nat.le_trans profile.1 (Nat.le_max_right _ _))⟩
    have enlarged : max 1 values.length * projectRows rows path.length ≤ projectRows rows (index :: path).length := by
      simp only [List.length_cons, projectRows_step]
      exact Nat.mul_le_mul_right _ count
    exact ⟨NodeShape.mono result merged.1 enlarged (Nat.le_refl _), by
      simp only [height]
      exact Nat.le_trans merged.2 (Nat.le_trans outputs.2.2 (Nat.le_succ _))⟩
  have recursiveCase : ∀ {original before exposed middle path index result after},
      SourceEqualityRequiredGraph.Recursive original → SourceEqualityRequiredHead.Head original before exposed middle →
      Project (Symbol := Symbol) (Guard := Guard) (index :: path) exposed middle result after →
      NodeResult (index :: path) exposed middle result after → NodeResult (index :: path) original before result after := by
    intro original before exposed middle path index result after recursive _ _ _ rows arity _ _ profile
    have domain := NodeShape.domain original profile
    cases domain <;> cases recursive
  have nilCase : ∀ {path state}, RowsResult path ([] : List (EdgeValue Symbol Guard)) state [] state := by
    intro path state rows arity _ _ _
    exact ⟨True.intro, Nat.le_refl _, Nat.le_refl _⟩
  have missingCase : ∀ {edge path index edges before results after}, select edge.children index = none →
      ProjectRows (Symbol := Symbol) (Guard := Guard) path index edges before results after →
      RowsResult path edges before results after → RowsResult path (edge :: edges) before results after := by
    intro edge path index edges before results after _ _ ih rows arity semantic resident profile
    have remaining := ih rows arity semantic (fun edge member => resident edge (List.mem_cons_of_mem _ member)) profile.2
    exact ⟨remaining.1, Nat.le_trans remaining.2.1 (Nat.le_succ _),
      Nat.le_trans remaining.2.2 (Nat.le_max_right _ _)⟩
  have selectedCase : ∀ {edge index child path before result middle edges results after},
      select edge.children index = some child → Project (Symbol := Symbol) (Guard := Guard) path child before result middle →
      ProjectRows path index edges middle results after → NodeResult path child before result middle →
      RowsResult path edges middle results after → RowsResult path (edge :: edges) before (result :: results) after := by
    intro edge index child path before result middle edges results after found actual _ firstIH restIH rows arity semantic resident profile
    have included := select_member found
    have childShape := ChildrenShape.member edge.children (EdgeShape.children edge profile.1) child included
    have available := semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge (resident edge List.mem_cons_self) child included
    have first := firstIH rows arity semantic available childShape
    have physical := SourceCurrentAllocatedFiniteOrdinaryProjection.project actual semantic available (NodeShape.domain child childShape)
    have remaining := restIH rows arity physical.2.1
      (fun edge member => edge_grows before middle physical.1.growth edge (resident edge (List.mem_cons_of_mem _ member))) profile.2
    refine ⟨⟨first.1, remaining.1⟩, Nat.succ_le_succ remaining.2.1, ?_⟩
    exact Nat.max_le.mpr ⟨Nat.le_trans first.2 (Nat.le_trans
      (SourceCurrentAllocatedFiniteOrdinaryDomain.child_le_edge edge child included) (Nat.le_max_left _ _)),
      Nat.le_trans remaining.2.2 (Nat.le_max_right _ _)⟩
  constructor
  · intro path value before result after actual
    exact Project.rec (motive_1 := fun path value before result after _ => NodeResult path value before result after)
      (motive_2 := fun path _ edges before results after _ => RowsResult path edges before results after)
      rootCase emptyCase ordinaryCase recursiveCase nilCase missingCase selectedCase actual
  · intro path index edges before results after actual
    exact ProjectRows.rec (motive_1 := fun path value before result after _ => NodeResult path value before result after)
      (motive_2 := fun path _ edges before results after _ => RowsResult path edges before results after)
      rootCase emptyCase ordinaryCase recursiveCase nilCase missingCase selectedCase actual

/-- Actual node projections derive the complete output profile and cannot increase height. -/
theorem project {rows arity : Nat} {path : List Int} {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : Project path value before result after) (semantic : SemanticReady before)
    (available : Available before value) (profile : NodeShape rows arity value) :
    NodeShape (projectRows rows path.length) arity result ∧ height result ≤ height value :=
  projection.1 _ _ _ _ _ actual rows arity semantic available profile

/-- Actual row projections retain output count, descendant profiles, and the original child-height maximum. -/
theorem rows {rowLimit arity : Nat} {path : List Int} {index : Int} {edges : List (EdgeValue Symbol Guard)}
    {results : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (actual : ProjectRows path index edges before results after) (semantic : SemanticReady before)
    (resident : Edges before edges) (profile : RowsShape rowLimit arity edges) :
    ChildrenShape (projectRows rowLimit path.length) arity results ∧ results.length ≤ edges.length ∧
      childrenHeight results ≤ edgesHeight edges :=
  projection.2 _ _ _ _ _ _ actual rowLimit arity semantic resident profile

/-- A supplied height limit follows the same actual projected node and its path envelope. -/
theorem project_bounded {rows arity : Nat} {path : List Int} {value result : Value Symbol Guard}
    {before after : State Symbol Guard} (actual : Project path value before result after)
    (semantic : SemanticReady before) (available : Available before value) (profile : NodeShape rows arity value)
    (bound : Nat) (bounded : height value ≤ bound) :
    NodeShape (projectRows rows path.length) arity result ∧ height result ≤ bound :=
  let checked := project actual semantic available profile
  ⟨checked.1, Nat.le_trans checked.2 bounded⟩

/-- Forest root union and signed child selection derive a common input-only profile and height bound. -/
theorem forest {rows arity : Nat} {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : State Symbol Guard} (actual : Forest path values before result after)
    (semantic : SemanticReady before) (available : Values before values) (profile : ChildrenShape rows arity values)
    (count bound : Nat) (lengthBound : values.length ≤ count) (heightBound : childrenHeight values ≤ bound) :
    NodeShape (forestRows rows count path.length) arity result ∧ height result ≤ bound := by
  cases actual with
  | root unionTrace =>
      have merged := union unionTrace semantic available profile
      have enlarged : max 1 values.length * rows ≤ forestRows rows count 0 := by
        apply Nat.mul_le_mul (Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans lengthBound (Nat.le_max_right _ _)⟩)
          (projectRows_base rows)
      exact ⟨NodeShape.mono result merged.1 enlarged (Nat.le_refl _), Nat.le_trans merged.2 heightBound⟩
  | missing => exact ⟨True.intro, Nat.zero_le _⟩
  | selected found body =>
      rename_i index selected path
      have member := select_member found
      have checked := project body semantic (available _ member) (ChildrenShape.member values profile _ member)
      have enlarged : projectRows rows path.length ≤ forestRows rows count (index :: path).length := by
        apply Nat.le_trans (projectRows_mono rows (Nat.le_succ path.length))
        simpa only [forestRows, List.length_cons, Nat.one_mul] using
          Nat.mul_le_mul_right (projectRows rows (path.length + 1)) (Nat.le_max_left 1 count)
      exact ⟨NodeShape.mono result checked.1 enlarged (Nat.le_refl _), Nat.le_trans checked.2
        (Nat.le_trans ((MergedOrdinaryHeight.childrenHeight_le _ _).mp heightBound _ member) (Nat.le_refl _))⟩

/-- Uniform input path and height limits bound the same actual node projection. -/
theorem project_uniform {rows arity : Nat} {path : List Int} {value result : Value Symbol Guard}
    {before after : State Symbol Guard} (actual : Project path value before result after)
    (semantic : SemanticReady before) (available : Available before value) (profile : NodeShape rows arity value)
    (depth bound : Nat) (pathBound : path.length ≤ depth) (heightBound : height value ≤ bound) :
    NodeShape (projectRows rows depth) arity result ∧ height result ≤ bound := by
  have checked := project_bounded actual semantic available profile bound heightBound
  exact ⟨NodeShape.mono result checked.1 (projectRows_mono rows pathBound) (Nat.le_refl _), checked.2⟩

/-- Uniform forest size, path length, and height limits bound the actual forest result. -/
theorem forest_uniform {rows arity : Nat} {path : List Int} {values : List (Value Symbol Guard)}
    {result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : Forest path values before result after) (semantic : SemanticReady before)
    (available : Values before values) (profile : ChildrenShape rows arity values)
    (count depth bound : Nat) (lengthBound : values.length ≤ count)
    (pathBound : path.length ≤ depth) (heightBound : childrenHeight values ≤ bound) :
    NodeShape (forestRows rows count depth) arity result ∧ height result ≤ bound := by
  have checked := forest actual semantic available profile count bound lengthBound heightBound
  exact ⟨NodeShape.mono result checked.1
    (Nat.mul_le_mul_left (max 1 count) (projectRows_mono rows pathBound)) (Nat.le_refl _), checked.2⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryProjectionProfile
