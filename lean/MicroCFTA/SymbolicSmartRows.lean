import MicroCFTA.SymbolicSourceUnion
import MicroCFTA.SymbolicGraphView

/-!
# Empty-child filtering in the source node constructor

`mkNode` removes an edge when one child is `EmptyNode`. It then interns the
set of surviving edges. The model uses duplicate-free lists for this set.
Only list order differs. These operations preserve constructor membership
and the numeric interpretation used by the source signed union loop.
-/
namespace MicroCFTA.SymbolicSmartRows
open Language SymbolicDriver

/-- The source `isEmptyEdge` test, with an explicit empty-node identity. -/
def isEmptyEdge (empty : Nat) (edge : SymbolicDriver.Edge Symbol) : Bool := edge.children.contains empty

/-- The node smart constructor removes empty children and repeated edge keys. -/
def smartRows [DecidableEq Symbol] (empty : Nat) (edges : List (SymbolicDriver.Edge Symbol)) :
    List (SymbolicDriver.Edge Symbol) :=
  (edges.filter fun edge => !isEmptyEdge empty edge).eraseDups

/-- The source node constructor retains exactly the distinct nonempty structural edges. -/
theorem smartRows_member [DecidableEq Symbol] (empty : Nat) (edges : List (SymbolicDriver.Edge Symbol))
    (edge : SymbolicDriver.Edge Symbol) :
    edge ∈ smartRows empty edges ↔ edge ∈ edges ∧ empty ∉ edge.children := by
  simp [smartRows, isEmptyEdge]

/-- A child-list membership proof supplies the corresponding accepted child term. -/
theorem all₂_child (relation : State → Value → Prop) (states : List State) (values : List Value)
    (runs : All₂ relation states values) (state : State) (member : state ∈ states) :
    ∃ value ∈ values, relation state value := by
  induction runs with
  | nil => cases member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_, by simp, head⟩
    · obtain ⟨value, present, accepted⟩ := ih member
      exact ⟨value, by simp [present], accepted⟩

/-- An empty child prevents constructor membership for every finite term. -/
theorem empty_child_impossible (language : Nat → List (Term Symbol)) (empty : Nat)
    (emptyLanguage : language empty = []) (edge : SymbolicDriver.Edge Symbol)
    (present : empty ∈ edge.children) (term : Term Symbol) : ¬ ShapeHolds language edge term := by
  rintro ⟨children, _, accepted⟩
  obtain ⟨child, _, member⟩ := all₂_child _ edge.children children accepted empty present
  simp [emptyLanguage] at member

/-- Removing an empty-child edge leaves every accepted constructor term available. -/
theorem smartRows_exact [DecidableEq Symbol] (language : Nat → List (Term Symbol)) (empty : Nat)
    (emptyLanguage : language empty = []) (edges : List (SymbolicDriver.Edge Symbol))
    (guard : SymbolicDriver.Edge Symbol → Term Symbol → Bool) (term : Term Symbol) :
    (∃ edge ∈ smartRows empty edges, ShapeHolds language edge term ∧ guard edge term = true) ↔
      ∃ edge ∈ edges, ShapeHolds language edge term ∧ guard edge term = true := by
  constructor
  · rintro ⟨edge, member, shape, acceptedGuard⟩
    exact ⟨edge, ((smartRows_member empty edges edge).mp member).1, shape, acceptedGuard⟩
  · rintro ⟨edge, member, shape, acceptedGuard⟩
    refine ⟨edge, (smartRows_member empty edges edge).mpr ⟨member, ?_⟩, shape, acceptedGuard⟩
    intro impossible
    exact empty_child_impossible language empty emptyLanguage edge impossible term shape

/-- A structurally empty edge has numeric value zero, even with arbitrary signed indicators. -/
theorem empty_child_zero (language : Nat → List (Term Symbol)) (empty : Nat)
    (emptyLanguage : language empty = []) (edge : SymbolicDriver.Edge Symbol)
    (present : empty ∈ edge.children) (term : Term Symbol) : edgeValue language term edge = 0 := by
  have absent := empty_child_impossible language empty emptyLanguage edge present term
  simp [edgeValue, absent, Lattice.indicator]

/-- The source singleton-node emptiness check is exactly the empty-child test. -/
theorem singleton_empty_iff [DecidableEq Symbol] (empty : Nat) (edge : SymbolicDriver.Edge Symbol) :
    smartRows empty [edge] = [] ↔ empty ∈ edge.children := by
  constructor
  · intro rejected
    by_cases present : empty ∈ edge.children
    · exact present
    · have retained := (smartRows_member empty [edge] edge).mpr ⟨by simp, present⟩
      simp [rejected] at retained
  · intro present
    simp [smartRows, isEmptyEdge, present]

/-- A rejected singleton intersection contributes zero to the source signed union. -/
theorem singleton_empty_zero [DecidableEq Symbol] (language : Nat → List (Term Symbol)) (empty : Nat)
    (emptyLanguage : language empty = []) (edge : SymbolicDriver.Edge Symbol)
    (rejected : smartRows empty [edge] = []) (term : Term Symbol) : edgeValue language term edge = 0 :=
  empty_child_zero language empty emptyLanguage edge ((singleton_empty_iff empty edge).mp rejected) term

/-- The actual empty-child filter preserves the complete inclusion-exclusion polynomial. -/
theorem source_union_filter_exact [DecidableEq Symbol] (language : Nat → List (Term Symbol))
    (graph : SymbolicDriver.Graph Symbol) (empty : Nat) (emptyLanguage : language empty = [])
    (intersection : ∀ left right term, term ∈ language (graph.intersect left right) ↔
      term ∈ language left ∧ term ∈ language right)
    (edges : List (SymbolicDriver.Edge Symbol)) (term : Term Symbol)
    (member : SymbolicDriver.Edge Symbol → Bool)
    (originals : ∀ edge ∈ edges, edgeValue language term edge = Lattice.indicator (member edge)) :
    Symbolic.weighted (edgeValue language term)
      (Symbolic.unionCoefficients
        (SymbolicSourceUnion.filteredMeet (SymbolicDriver.intersectEdge graph) (fun edge => !isEmptyEdge empty edge)) edges) =
    Symbolic.weighted (edgeValue language term)
      (Symbolic.unionCoefficients (SymbolicDriver.intersectEdge graph) edges) := by
  apply SymbolicSourceUnion.union_filter_exact _ member _ _
    (edgeValue_intersection language graph intersection term) ?_ edges originals
  intro edge rejected
  apply empty_child_zero language empty emptyLanguage edge ?_ term
  simpa [isEmptyEdge] using rejected

end MicroCFTA.SymbolicSmartRows
