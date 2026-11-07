import MicroCFTA.InternedOrdinaryUnionReadback
import MicroCFTA.InternedUnionFilterFusion

/-!
# Ordinary and union height above recursive records

The height counts both ordinary nodes and explicit union records.
Empty values, references, and Mu records have height zero.
The restriction to the actual type universe is a separate invariant.
An ordinary merge preserves the input maximum. General union construction
can add one union layer above that maximum.
-/
namespace MicroCFTA.SourceSynthesisUniversePrefixHeight
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedFreshProbeKeys InternedEdgeResidency InternedNormalizationFree
open InternedBinderProtocol (NodeKey Reference)
open InternedOrdinaryUnionReadback (Ordinary)

variable {Symbol Guard : Type}

mutual
/-- Count ordinary and union layers before a recursive or reference boundary. -/
def height : Value Symbol Guard → Nat
  | .node _ edges _ _ => edgesHeight edges + 1
  | .union _ members _ _ => childrenHeight members + 1
  | _ => 0

/-- The height below one row is the greatest height of its children. -/
def edgeHeight : EdgeValue Symbol Guard → Nat
  | .mk _ children => childrenHeight children

/-- The height below an ordinary node is the greatest height below a row. -/
def edgesHeight : List (EdgeValue Symbol Guard) → Nat
  | [] => 0
  | first :: rest => max (edgeHeight first) (edgesHeight rest)

/-- The height of a finite child list is the greatest member height. -/
def childrenHeight : List (Value Symbol Guard) → Nat
  | [] => 0
  | first :: rest => max (height first) (childrenHeight rest)
end

/-- A row maximum is bounded exactly when every row is bounded. -/
theorem edgesHeight_le (edges : List (EdgeValue Symbol Guard)) (bound : Nat) :
    edgesHeight edges ≤ bound ↔ ∀ edge ∈ edges, edgeHeight edge ≤ bound := by
  induction edges with
  | nil => simp [edgesHeight]
  | cons first rest ih => simp [edgesHeight, Nat.max_le, ih]

/-- A child maximum is bounded exactly when every child is bounded. -/
theorem childrenHeight_le (children : List (Value Symbol Guard)) (bound : Nat) :
    childrenHeight children ≤ bound ↔ ∀ child ∈ children, height child ≤ bound := by
  induction children with
  | nil => simp [childrenHeight]
  | cons first rest ih => simp [childrenHeight, Nat.max_le, ih]

/-- Every actual ordinary child has strictly smaller height than its parent. -/
theorem child_lt (entry : Interned NodeKey) (edges : List (EdgeValue Symbol Guard))
    (depth : Nat) (free : List Reference) (edge : EdgeValue Symbol Guard) (present : edge ∈ edges)
    (child : Value Symbol Guard) (member : child ∈ edge.children) :
    height child < height (.node entry edges depth free) := by
  have rowBound := (edgesHeight_le edges (edgesHeight edges)).mp (Nat.le_refl _) edge present
  have childBound : height child ≤ edgeHeight edge := by
    cases edge with
    | mk entry children => exact (childrenHeight_le children (childrenHeight children)).mp (Nat.le_refl _) child member
  simp only [height]
  omega

/-- Every explicit union member has strictly smaller height than its parent. -/
theorem member_lt (entry : Interned NodeKey) (members : List (Value Symbol Guard))
    (depth : Nat) (free : List Reference) (child : Value Symbol Guard) (member : child ∈ members) :
    height child < height (.union entry members depth free) := by
  have bound := (childrenHeight_le members (childrenHeight members)).mp (Nat.le_refl _) child member
  simp only [height]
  omega

/-- Flattening a root union cannot increase any selected member's height. -/
theorem unionMembers_le (value child : Value Symbol Guard) (member : child ∈ unionMembers value) :
    height child ≤ height value := by
  cases value with
  | empty => simp [unionMembers] at member
  | union entry members depth free => exact Nat.le_of_lt (member_lt entry members depth free child member)
  | reference | node | mu =>
      simp only [unionMembers, List.mem_singleton] at member
      subst child
      exact Nat.le_refl _

/-- Actual canonical node construction respects every supplied raw-row height bound. -/
theorem makeNode_bound [DecidableEq (EdgeKey Symbol Guard)]
    (edges : List (EdgeValue Symbol Guard)) (state : InternedConstructorTemplates.State Symbol Guard)
    (facts : Facts state) (resident : ∀ edge ∈ edges, EdgeResident state edge) (bound : Nat)
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
    obtain ⟨entry, readback⟩ := identifyNode_readback (first :: rest) state facts.coherent facts.linked
      (by simpa only [same] using selected)
    simp only [run, readback, identifyNode, height]
    have positive := selectedBound first (by simp [same])
    have maximum : edgesHeight (first :: rest) ≤ bound - 1 := by
      apply (edgesHeight_le _ _).mpr
      intro edge member
      have below := selectedBound edge (by simpa only [same] using member)
      omega
    omega

/-- Actual ordinary-row concatenation does not exceed its operands' maximum height. -/
theorem ordinaryUnion_bound [DecidableEq (EdgeKey Symbol Guard)]
    (values : List (Value Symbol Guard)) (state : InternedConstructorTemplates.State Symbol Guard)
    (facts : Facts state) (resident : ∀ value ∈ values, Resident state value) :
    height (run (makeNode (values.flatMap nodeEdges)) state).1 ≤ childrenHeight values := by
  apply makeNode_bound _ state facts
  · intro edge member
    obtain ⟨value, included, selected⟩ := List.mem_flatMap.mp member
    exact resident_edges state facts.linked value (resident value included) edge selected
  · intro edge member
    obtain ⟨value, included, selected⟩ := List.mem_flatMap.mp member
    have bound := (childrenHeight_le values (childrenHeight values)).mp (Nat.le_refl _) value included
    cases value <;> simp only [nodeEdges] at selected <;> try contradiction
    case node entry edges depth free =>
      have rowBound := (edgesHeight_le edges (edgesHeight edges)).mp (Nat.le_refl _) edge selected
      simp only [height] at bound
      omega

private theorem selected_bound (values : List (Value Symbol Guard)) :
    ∀ child ∈ distinctNodes (values.flatMap unionMembers), height child ≤ childrenHeight values := by
  intro child member
  obtain ⟨value, included, selected⟩ := List.mem_flatMap.mp (distinctNodes_member _ child member)
  exact Nat.le_trans (unionMembers_le value child selected)
    ((childrenHeight_le values (childrenHeight values)).mp (Nat.le_refl _) value included)

private theorem ordinary_request_bound [DecidableEq (EdgeKey Symbol Guard)]
    (values : List (Value Symbol Guard)) (edges : List (EdgeValue Symbol Guard))
    (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (available : ∀ value ∈ values, Available state value) (found : ordinaryEdges values = some edges) :
    height (run (makeNode edges) state).1 ≤ childrenHeight values := by
  have ordinary : ∀ value ∈ values, Ordinary value := by
    intro value member
    obtain ⟨entry, own, depth, free, same, _⟩ :=
      InternedUnionDescendants.ordinaryEdges_contains values edges found value member
    exact ⟨entry, own, depth, free, same⟩
  have rows := InternedOrdinaryUnionReadback.ordinaryEdges_eq values ordinary
  rw [found] at rows
  rw [Option.some.inj rows]
  exact ordinaryUnion_bound values state facts (fun value member => (available value member).resident)

/-- General actual union construction can add at most one layer above the input maximum. -/
theorem makeUnion_bound [DecidableEq (EdgeKey Symbol Guard)]
    (values : List (Value Symbol Guard)) (state : InternedConstructorTemplates.State Symbol Guard)
    (facts : Facts state) (available : ∀ value ∈ values, Available state value) :
    height (run (makeUnion values) state).1 ≤ childrenHeight values + 1 := by
  have bounded := selected_bound values
  have selectedAvailable := InternedUnionFilterFusion.selected_available values state available
  cases normalized : distinctNodes (values.flatMap unionMembers) with
  | nil => simp only [makeUnion, normalized, run, height]; omega
  | cons first rest =>
      cases rest with
      | nil =>
          have below := bounded first (by simp only [normalized, List.mem_singleton])
          simp only [makeUnion, normalized, run]
          omega
      | cons second tail =>
          have inputs : ∀ value ∈ first :: second :: tail, Available state value := by
            intro value member
            exact selectedAvailable value (by simpa only [normalized] using member)
          have maximum : childrenHeight (first :: second :: tail) ≤ childrenHeight values := by
            apply (childrenHeight_le _ _).mpr
            intro value member
            exact bounded value (by simpa only [normalized] using member)
          cases ordinary : ordinaryEdges (first :: second :: tail) with
          | some edges =>
              have below := ordinary_request_bound (first :: second :: tail) edges state facts inputs ordinary
              have total := Nat.le_trans below (Nat.le_trans maximum (Nat.le_succ (childrenHeight values)))
              simpa only [makeUnion, normalized, ordinary] using total
          | none =>
              obtain ⟨entry, readback⟩ := InternedUnionFilterFusion.union_readback
                values first second tail state facts available normalized ordinary
              rw [readback, height]
              omega

/-- Actual union construction on ordinary operands preserves their maximum height. -/
theorem makeUnion_ordinary_bound [DecidableEq (EdgeKey Symbol Guard)]
    (values : List (Value Symbol Guard)) (state : InternedConstructorTemplates.State Symbol Guard)
    (facts : Facts state) (available : ∀ value ∈ values, Available state value)
    (ordinary : ∀ value ∈ values, Ordinary value) :
    height (run (makeUnion values) state).1 ≤ childrenHeight values := by
  have flattened := InternedOrdinaryUnionReadback.flatten_ordinary values ordinary
  have bounded := selected_bound values
  have selectedAvailable := InternedUnionFilterFusion.selected_available values state available
  have selectedOrdinary : ∀ value ∈ distinctNodes (values.flatMap unionMembers), Ordinary value := by
    rw [flattened]
    intro value member
    exact ordinary value (distinctNodes_member values value member)
  cases normalized : distinctNodes (values.flatMap unionMembers) with
  | nil => simp only [makeUnion, normalized, run, height]; exact Nat.zero_le _
  | cons first rest =>
      cases rest with
      | nil =>
          simpa only [makeUnion, normalized, run] using bounded first (by simp only [normalized, List.mem_singleton])
      | cons second tail =>
          have inputs : ∀ value ∈ first :: second :: tail, Available state value := by
            intro value member
            exact selectedAvailable value (by simpa only [normalized] using member)
          have ownOrdinary : ∀ value ∈ first :: second :: tail, Ordinary value := by
            simpa only [normalized] using selectedOrdinary
          have request := InternedOrdinaryUnionReadback.ordinaryEdges_eq (first :: second :: tail) ownOrdinary
          have below := ordinary_request_bound (first :: second :: tail) _ state facts inputs request
          have maximum : childrenHeight (first :: second :: tail) ≤ childrenHeight values := by
            apply (childrenHeight_le _ _).mpr
            intro value member
            exact bounded value (by simpa only [normalized] using member)
          simpa only [makeUnion, normalized, request] using Nat.le_trans below maximum

end MicroCFTA.SourceSynthesisUniversePrefixHeight
