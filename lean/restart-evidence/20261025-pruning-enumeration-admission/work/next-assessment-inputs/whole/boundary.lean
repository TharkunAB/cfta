import MicroCFTA.InternedNormalizationDepth

/-!
# Ordinary constructor height for guarded recursive merging

The merge worker stops at recursive and union records. Ordinary constructor
height therefore ignores their contents. Direct child calls decrease this
height. Ordinary column unions retain the maximum height of their inputs.
-/
namespace MicroCFTA.MergedOrdinaryHeight
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedEdgeResidency InternedFreshProbeKeys

mutual
/-- Count ordinary constructor layers and stop at every recursive or union boundary. -/
def height : Value Symbol Guard → Nat
  | .node _ edges _ _ => edgesHeight edges + 1
  | _ => 0

/-- The height below an edge is the maximum height of its children. -/
def edgeHeight : EdgeValue Symbol Guard → Nat
  | .mk _ children => childrenHeight children

/-- The greatest child height in an ordered edge list. -/
def edgesHeight : List (EdgeValue Symbol Guard) → Nat
  | [] => 0
  | edge :: rest => max (edgeHeight edge) (edgesHeight rest)

/-- The greatest height in an ordered list of complete child records. -/
def childrenHeight : List (Value Symbol Guard) → Nat
  | [] => 0
  | child :: rest => max (height child) (childrenHeight rest)
end

/-- A maximum of edge heights is bounded exactly when every edge is bounded. -/
theorem edgesHeight_le (edges : List (EdgeValue Symbol Guard)) (bound : Nat) :
    edgesHeight edges ≤ bound ↔ ∀ edge ∈ edges, edgeHeight edge ≤ bound := by
  induction edges with
  | nil => simp [edgesHeight]
  | cons edge rest ih => simp [edgesHeight, Nat.max_le, ih]

/-- A maximum of child heights is bounded exactly when every child is bounded. -/
theorem childrenHeight_le (children : List (Value Symbol Guard)) (bound : Nat) :
    childrenHeight children ≤ bound ↔ ∀ child ∈ children, height child ≤ bound := by
  induction children with
  | nil => simp [childrenHeight]
  | cons child rest ih => simp [childrenHeight, Nat.max_le, ih]

/-- Every immediate ordinary child is strictly below its parent. -/
theorem child_lt (entry : Interned InternedBinderProtocol.NodeKey)
    (edges : List (EdgeValue Symbol Guard)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (edge : EdgeValue Symbol Guard) (present : edge ∈ edges)
    (child : Value Symbol Guard) (member : child ∈ edge.children) :
    height child < height (.node entry edges depth free) := by
  have edgeBound := (edgesHeight_le edges (edgesHeight edges)).mp (Nat.le_refl _) edge present
  have childBound : height child ≤ edgeHeight edge := by
    cases edge with
    | mk entry children => exact (childrenHeight_le children (childrenHeight children)).mp (Nat.le_refl _) child member
  simp only [height]
  omega

/-- Canonical node construction does not exceed the heights of its complete source edges. -/
theorem makeNode_bound [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (linked : Linked state)
    (resident : ∀ edge ∈ edges, EdgeResident state edge) (bound : Nat)
    (bounded : ∀ edge ∈ edges, edgeHeight edge + 1 ≤ bound) :
    height (run (makeNode edges) state).1 ≤ bound := by
  have selected : ∀ edge ∈ canonicalEdges (surviving edges), EdgeResident state edge :=
    fun edge member => resident edge (List.mem_filter.mp (canonicalEdges_member _ edge member)).1
  have selectedBound : ∀ edge ∈ canonicalEdges (surviving edges), edgeHeight edge + 1 ≤ bound :=
    fun edge member => bounded edge (List.mem_filter.mp (canonicalEdges_member _ edge member)).1
  unfold makeNode
  dsimp only
  split
  · exact Nat.zero_le _
  · rename_i first rest same
    obtain ⟨entry, exactResult⟩ := identifyNode_readback (first :: rest) state coherent linked
      (by simpa [same] using selected)
    simp only [run, exactResult, identifyNode, height]
    have positive := selectedBound first (by simp [same])
    have maximum : edgesHeight (first :: rest) ≤ bound - 1 := by
      apply (edgesHeight_le _ _).mpr
      intro edge member
      have bounded := selectedBound edge (by simpa [same] using member)
      omega
    omega

/-- The source recursive-boundary test stops at Mu and explicit union records. -/
def recursiveBoundary : Value Symbol Guard → Bool
  | .mu .. | .union .. => true
  | _ => false

/-- A closed operand without a recursive boundary is empty or an ordinary node. -/
theorem ordinary_operand (value : Value Symbol Guard) (closed : value.free = [])
    (clear : recursiveBoundary value = false) :
    value = .empty ∨ ∃ entry edges depth free, value = .node entry edges depth free := by
  cases value <;> simp_all [recursiveBoundary, Value.free]

/-- Every actual child of a closed ordinary record is closed. -/
theorem closed_child (state : State Symbol Guard) (coherent : Coherent state)
    (entry : Interned InternedBinderProtocol.NodeKey) (edges : List (EdgeValue Symbol Guard))
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (resident : Resident state (.node entry edges depth free)) (closed : free = [])
    (edge : EdgeValue Symbol Guard) (present : edge ∈ edges)
    (child : Value Symbol Guard) (member : child ∈ edge.children) : child.free = [] := by
  have recorded := InternedNormalizationFree.node_free state coherent entry edges depth free resident
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro name included
  have parent : name ∈ childFree (edges.flatMap EdgeValue.children) :=
    (childFree_member _ _).mpr
      ⟨child, List.mem_flatMap.mpr ⟨edge, present, member⟩, included⟩
  rw [← recorded, closed] at parent
  cases parent

/-- The actual boundary guard leaves only ordinary or empty retained column operands. -/
theorem guarded_column_ordinary (state : State Symbol Guard) (coherent : Coherent state)
    (entry : Interned InternedBinderProtocol.NodeKey) (edges : List (EdgeValue Symbol Guard))
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (resident : Resident state (.node entry edges depth free)) (closed : free = [])
    (values : List (Value Symbol Guard))
    (selected : ∀ value ∈ values, ∃ edge ∈ edges, value ∈ edge.children)
    (guarded : values.any recursiveBoundary = false) :
    ∀ value ∈ values, value = .empty ∨ ∃ entry edges depth free, value = .node entry edges depth free := by
  intro value member
  obtain ⟨edge, present, included⟩ := selected value member
  exact ordinary_operand value (closed_child state coherent entry edges depth free resident closed edge present value included)
    (by simpa using (List.any_eq_false.mp guarded) value member)

/-- The source union fast path concatenates the complete ordinary edge records. -/
def ordinaryUnion (values : List (Value Symbol Guard)) : Work Symbol Guard (Value Symbol Guard) :=
  makeNode (values.flatMap nodeEdges)

/-- An ordinary source union cannot increase its operands' maximum constructor height. -/
theorem ordinaryUnion_bound [DecidableEq (EdgeKey Symbol Guard)]
    (values : List (Value Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) (linked : Linked state)
    (resident : ∀ value ∈ values, Resident state value) (bound : Nat)
    (bounded : ∀ value ∈ values, height value ≤ bound) :
    height (run (ordinaryUnion values) state).1 ≤ bound := by
  apply makeNode_bound _ state coherent linked
  · intro edge member
    obtain ⟨value, present, included⟩ := List.mem_flatMap.mp member
    exact resident_edges state linked value (resident value present) edge included
  · intro edge member
    obtain ⟨value, present, included⟩ := List.mem_flatMap.mp member
    have below := bounded value present
    cases value <;> simp only [nodeEdges] at included <;> try contradiction
    case node entry edges depth free =>
      have edgeBound := (edgesHeight_le edges (edgesHeight edges)).mp (Nat.le_refl _) edge included
      simp only [height] at below
      omega

/-- Every retained child column lies strictly below the original ordinary root. -/
theorem column_union_lt [DecidableEq (EdgeKey Symbol Guard)]
    (entry : Interned InternedBinderProtocol.NodeKey) (edges : List (EdgeValue Symbol Guard))
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (values : List (Value Symbol Guard))
    (selected : ∀ value ∈ values, ∃ edge ∈ edges, value ∈ edge.children)
    (state : State Symbol Guard) (coherent : Coherent state) (linked : Linked state)
    (resident : ∀ value ∈ values, Resident state value) :
    height (run (ordinaryUnion values) state).1 < height (.node entry edges depth free) := by
  have bound := ordinaryUnion_bound values state coherent linked resident (edgesHeight edges) (by
    intro value member
    obtain ⟨edge, present, included⟩ := selected value member
    have less := child_lt entry edges depth free edge present value included
    simp only [height] at less
    omega)
  simp only [height]
  omega

/-- Filtering and duplicate removal cannot invalidate a child-column height bound. -/
theorem selected_column (children : List (Value Symbol Guard)) (keep : Value Symbol Guard → Bool)
    (edges : List (EdgeValue Symbol Guard))
    (selected : ∀ child ∈ children, ∃ edge ∈ edges, child ∈ edge.children) :
    ∀ child ∈ distinctNodes (children.filter keep), ∃ edge ∈ edges, child ∈ edge.children := by
  intro child member
  exact selected child (List.mem_filter.mp (distinctNodes_member _ child member)).1

end MicroCFTA.MergedOrdinaryHeight
