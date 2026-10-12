import MicroCFTA.EnumerationEquality
import MicroCFTA.BoundDepth

/-!
# Bounded constructor rows for complete enumeration

The worker starts with exposed constructor rows. It uses remaining height
and source identity as the memo key. It retains symbols and constraints,
copies every ordered child, and removes rows with empty bounded children.
The output has only constructor and empty node views. Binder unfolding and
runtime identity allocation remain separate representation steps.
-/

namespace MicroCFTA.EnumerationBoundedRows
open Language EnumerationState EnumerationSemantics EnumerationCorrectness SymbolicGraphView

/-- Copy the ordered children and retain all source constraints. -/
def copyEdge (encode : Nat × Nat → Nat) (remaining : Nat) (edge : EnumerationState.Edge Symbol Guard) : EnumerationState.Edge Symbol Guard :=
  {edge with children := edge.children.map (fun child => encode (remaining, child))}

/-- The constructor branch of `boundDepth`, including source empty-child cleanup. -/
def rows (encode : Nat × Nat → Nat) (source : Nat → List (EnumerationState.Edge Symbol Guard)) :
    Nat → Nat → List (EnumerationState.Edge Symbol Guard)
  | 0, _ => []
  | remaining + 1, node =>
      (((source node).filter (fun edge => decide (0 < remaining) || edge.children.isEmpty)).filter
        (fun edge => edge.children.all (fun child => !(rows encode source remaining child).isEmpty))).map
        (copyEdge encode remaining)

/-- Read the constructed rows as source enumeration nodes. -/
def graph (encode : Nat × Nat → Nat) (decode : Nat → Nat × Nat)
    (source : Nat → List (EnumerationState.Edge Symbol Guard)) (meet : Nat → Nat → Nat) : Graph Symbol Guard where
  node identity := match rows encode source (decode identity).1 (decode identity).2 with
    | [] => .empty
    | edge :: rest => .alternatives (edge :: rest)
  intersect := meet

/-- Bounded construction preserves the source edge invariant at every height. -/
theorem rows_valid (encode : Nat × Nat → Nat) (source : Nat → List (EnumerationState.Edge Symbol Guard))
    (valid : ∀ node edge, edge ∈ source node → ValidEdge edge) (height node : Nat)
    (edge : EnumerationState.Edge Symbol Guard) (member : edge ∈ rows encode source height node) : ValidEdge edge := by
  cases height with
  | zero => simp [rows] at member
  | succ remaining =>
      obtain ⟨original, filtered, rfl⟩ := List.mem_map.mp member
      exact EnumerationConstructors.setChildren_valid original _ (by simp)
        (valid node original (List.mem_filter.mp (List.mem_filter.mp filtered).1).1)

/-- Bounded constructor output derives complete node classification and valid edge tries. -/
theorem complete (encode : Nat × Nat → Nat) (decode : Nat → Nat × Nat)
    (source : Nat → List (EnumerationState.Edge Symbol Guard)) (meet : Nat → Nat → Nat)
    (valid : ∀ node edge, edge ∈ source node → ValidEdge edge) : CompleteGraph (graph encode decode source meet) := by
  constructor
  · intro node body
    cases found : rows encode source (decode node).1 (decode node).2 <;> simp [graph, found]
  · intro node edges view edge member
    have present : edge ∈ rows encode source (decode node).1 (decode node).2 := by
      cases found : rows encode source (decode node).1 (decode node).2 with
      | nil => simp [graph, found] at view
      | cons first rest =>
          simp only [graph, found, Node.alternatives.injEq] at view
          simpa only [view] using member
    exact rows_valid encode source valid _ _ edge present

/-- The guarded row view reads precisely the generated constructor list. -/
theorem graph_rows (encode : Nat × Nat → Nat) (decode : Nat → Nat × Nat)
    (source : Nat → List (EnumerationState.Edge Symbol Guard)) (meet : Nat → Nat → Nat)
    (meaning : Guard → Term Symbol → Prop) (identity : Nat) :
    EnumerationLanguage.automaton (graph encode decode source meet) meaning identity =
      (rows encode source (decode identity).1 (decode identity).2).map (EnumerationLanguage.edgeView meaning) := by
  cases found : rows encode source (decode identity).1 (decode identity).2 <;> simp [EnumerationLanguage.automaton, graph, found]

/-- Constraint readback commutes with ordered child copying. -/
theorem copy_view (encode : Nat × Nat → Nat) (remaining : Nat) (meaning : Guard → Term Symbol → Prop)
    (edge : EnumerationState.Edge Symbol Guard) :
    EnumerationLanguage.edgeView meaning (copyEdge encode remaining edge) =
      renameEdge encode (BoundDepth.copyEdge remaining (EnumerationLanguage.edgeView meaning edge)) := by
  classical
  simp [EnumerationLanguage.edgeView, copyEdge, renameEdge, BoundDepth.copyEdge, List.map_map, Function.comp_def]
  funext term
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_iff, Bool.and_eq_true]
  exact decide_eq_true_iff

/-- Empty-child cleanup is an instance of the proved exact normalized-row transformation. -/
noncomputable def normalized (encode : Nat × Nat → Nat) (decode : Nat → Nat × Nat)
    (roundtrip : ∀ key, decode (encode key) = key)
    (source : Nat → List (EnumerationState.Edge Symbol Guard)) (meet : Nat → Nat → Nat)
    (meaning : Guard → Term Symbol → Prop) :
    NormalizedRows (BoundDepth.bound (fun node => (source node).map (EnumerationLanguage.edgeView meaning)))
      (EnumerationLanguage.automaton (graph encode decode source meet) meaning) encode where
  keep _ edge := edge.children.all fun child =>
    !(EnumerationLanguage.automaton (graph encode decode source meet) meaning (encode child)).isEmpty
  members key edge := by
    obtain ⟨height, node⟩ := key
    rw [graph_rows, roundtrip]
    cases height with
    | zero => simp [rows, BoundDepth.bound]
    | succ remaining =>
        constructor
        · intro member
          obtain ⟨bounded, listed, rfl⟩ := List.mem_map.mp member
          obtain ⟨original, filtered, rfl⟩ := List.mem_map.mp listed
          obtain ⟨sourceFiltered, childrenKept⟩ := List.mem_filter.mp filtered
          obtain ⟨present, shallow⟩ := List.mem_filter.mp sourceFiltered
          refine ⟨BoundDepth.copyEdge remaining (EnumerationLanguage.edgeView meaning original), ?_, ?_, copy_view _ _ _ _⟩
          · exact List.mem_map.mpr ⟨EnumerationLanguage.edgeView meaning original,
              List.mem_filter.mpr ⟨List.mem_map.mpr ⟨original, present, rfl⟩, shallow⟩, rfl⟩
          · simpa [BoundDepth.copyEdge, EnumerationLanguage.edgeView, List.all_map, Function.comp_def,
              graph_rows, roundtrip] using childrenKept
        · rintro ⟨original, present, kept, rfl⟩
          obtain ⟨base, filtered, rfl⟩ := List.mem_map.mp present
          obtain ⟨mapped, shallow⟩ := List.mem_filter.mp filtered
          obtain ⟨edge, member, rfl⟩ := List.mem_map.mp mapped
          rw [← copy_view]
          apply List.mem_map.mpr
          refine ⟨copyEdge encode remaining edge, ?_, rfl⟩
          apply List.mem_map.mpr
          refine ⟨edge, List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨member, shallow⟩, ?_⟩, rfl⟩
          simpa [BoundDepth.copyEdge, EnumerationLanguage.edgeView, List.all_map, Function.comp_def,
            graph_rows, roundtrip] using kept
  rejected _ edge _ rejected := by
    have empty : ∃ child ∈ edge.children,
        EnumerationLanguage.automaton (graph encode decode source meet) meaning (encode child) = [] := by
      simpa using rejected
    exact Or.inr empty

/-- The constructed graph has exactly the source finite terms within the selected height. -/
theorem accepted_exact (encode : Nat × Nat → Nat) (decode : Nat → Nat × Nat)
    (roundtrip : ∀ key, decode (encode key) = key)
    (source : Nat → List (EnumerationState.Edge Symbol Guard)) (meet : Nat → Nat → Nat)
    (valid : ∀ node edge, edge ∈ source node → ValidEdge edge)
    (meaning : Guard → Term Symbol → Prop) (height node : Nat) (term : Term Symbol) :
    Accepted (graph encode decode source meet) meaning (encode (height, node)) term ↔
      Accepts (fun state => (source state).map (EnumerationLanguage.edgeView meaning)) node term ∧ term.height ≤ height := by
  rw [EnumerationLanguage.accepted_iff _ _ (complete encode decode source meet valid)]
  exact (normalizedRows_exact _ _ _ (normalized encode decode roundtrip source meet meaning) (height, node) term).trans
    (BoundDepth.bound_exact _ height node term)

/-- Every identity reads the bounded key supplied by the identity table. -/
theorem accepted_decoded (encode : Nat × Nat → Nat) (decode : Nat → Nat × Nat)
    (roundtrip : ∀ key, decode (encode key) = key)
    (source : Nat → List (EnumerationState.Edge Symbol Guard)) (meet : Nat → Nat → Nat)
    (valid : ∀ node edge, edge ∈ source node → ValidEdge edge)
    (meaning : Guard → Term Symbol → Prop) (identity : Nat) (term : Term Symbol) :
    Accepted (graph encode decode source meet) meaning identity term ↔
      Accepts (fun state => (source state).map (EnumerationLanguage.edgeView meaning)) (decode identity).2 term ∧
        term.height ≤ (decode identity).1 := by
  have same : Accepted (graph encode decode source meet) meaning identity term ↔
      Accepted (graph encode decode source meet) meaning (encode (decode identity)) term := by
    simp only [EnumerationLanguage.accepted_iff _ _ (complete encode decode source meet valid)]
    cases term with
    | node symbol children =>
        simp only [accepts_node_iff, graph_rows, roundtrip]
  exact same.trans (accepted_exact encode decode roundtrip source meet valid meaning _ _ term)

/-- Intersect the source identities and retain the smaller remaining height. -/
def boundedMeet (encode : Nat × Nat → Nat) (decode : Nat → Nat × Nat) (meet : Nat → Nat → Nat)
    (left right : Nat) : Nat :=
  encode (min (decode left).1 (decode right).1, meet (decode left).2 (decode right).2)

/-- Intersection of bounded languages follows from source constructor-row intersection. -/
theorem intersection_correct [DecidableEq Symbol] (encode : Nat × Nat → Nat) (decode : Nat → Nat × Nat)
    (roundtrip : ∀ key, decode (encode key) = key)
    (source : Nat → List (EnumerationState.Edge Symbol Guard)) (meet : Nat → Nat → Nat)
    (valid : ∀ node edge, edge ∈ source node → ValidEdge edge)
    (meaning : Guard → Term Symbol → Prop)
    (sourceRows : EnumerationIntersection.HashRows (fun state => (source state).map (EnumerationLanguage.edgeView meaning)) meet) :
    IntersectionCorrect (graph encode decode source (boundedMeet encode decode meet))
      (Accepted (graph encode decode source (boundedMeet encode decode meet)) meaning) := by
  intro left right term
  simp only [accepted_decoded encode decode roundtrip source _ valid meaning]
  change (Accepts _ (decode (boundedMeet encode decode meet left right)).2 term ∧
    term.height ≤ (decode (boundedMeet encode decode meet left right)).1) ↔ _
  simp only [boundedMeet, roundtrip]
  rw [productRows_exact _ meet (sourceRows.product _ _) (decode left).2 (decode right).2 term]
  simp only [Nat.le_min]
  exact ⟨fun ⟨⟨a, b⟩, c, d⟩ => ⟨⟨a, c⟩, b, d⟩, fun ⟨⟨a, c⟩, b, d⟩ => ⟨⟨a, b⟩, c, d⟩⟩

/-- The complete actual driver enumerates precisely the finite source terms within the bound. -/
theorem runs_exact [DecidableEq Symbol] (encode : Nat × Nat → Nat) (decode : Nat → Nat × Nat)
    (roundtrip : ∀ key, decode (encode key) = key)
    (source : Nat → List (EnumerationState.Edge Symbol Guard)) (meet : Nat → Nat → Nat)
    (valid : ∀ node edge, edge ∈ source node → ValidEdge edge)
    (meaning : Guard → Term Symbol → Prop)
    (sourceRows : EnumerationIntersection.HashRows (fun state => (source state).map (EnumerationLanguage.edgeView meaning)) meet)
    (marker : Symbol) (height node : Nat) (term : Term Symbol) :
    (Accepts (fun state => (source state).map (EnumerationLanguage.edgeView meaning)) node term ∧ term.height ≤ height) ↔
      ∃ fuel pending after, .ok ((term, pending), after) ∈
        runs (graph encode decode source (boundedMeet encode decode meet)) marker fuel (encode (height, node)) ∧
        ∀ obligation ∈ pending, meaning obligation.1 obligation.2 := by
  rw [← accepted_exact encode decode roundtrip source _ valid meaning height node term]
  exact EnumerationExact.runs_exact _ meaning (complete encode decode source _ valid)
    (intersection_correct encode decode roundtrip source meet valid meaning sourceRows) marker _ term

end MicroCFTA.EnumerationBoundedRows
