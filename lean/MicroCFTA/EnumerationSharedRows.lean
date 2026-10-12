import MicroCFTA.EnumerationBoundedRows

/-!
# Bounded row readback with shared identities

The source can intern equal bounded outputs under one identity. This adapter
uses the identity returned for each memo key. It does not require those
identities to be distinct or to decode back to the memo key.
-/

namespace MicroCFTA.EnumerationSharedRows
open Language EnumerationState EnumerationSemantics EnumerationCorrectness SymbolicGraphView

/-- Read only the constructor alternatives of an enumeration node. -/
def nodeRows (graph : Graph Symbol Guard) (identity : Nat) : List (EnumerationState.Edge Symbol Guard) :=
  match graph.node identity with | .alternatives edges => edges | _ => []

/-- Guard interpretation does not change which constructor rows are empty. -/
theorem automaton_rows (graph : Graph Symbol Guard) (meaning : Guard → Term Symbol → Prop) (identity : Nat) :
    EnumerationLanguage.automaton graph meaning identity = (nodeRows graph identity).map (EnumerationLanguage.edgeView meaning) := by
  cases found : graph.node identity <;> simp [EnumerationLanguage.automaton, nodeRows, found]

/-- One source constructor step uses the already computed bounded child identities. -/
def construct (encode : Nat × Nat → Nat) (lookup : Nat → List (EnumerationState.Edge Symbol Guard))
    (source : Nat → List (EnumerationState.Edge Symbol Guard)) : Nat → Nat → List (EnumerationState.Edge Symbol Guard)
  | 0, _ => []
  | remaining + 1, node =>
      (((source node).filter (fun edge => decide (0 < remaining) || edge.children.isEmpty)).filter
        (fun edge => edge.children.all (fun child => !(lookup (encode (remaining, child))).isEmpty))).map
        (EnumerationBoundedRows.copyEdge encode remaining)

/-- Set readback permits equal memo results to share one interned identity. -/
def Readback (source : Nat → List (EnumerationState.Edge Symbol Guard)) (target : Graph Symbol Guard)
    (encode : Nat × Nat → Nat) : Prop :=
  ∀ height node edge, edge ∈ nodeRows target (encode (height, node)) ↔
    edge ∈ construct encode (nodeRows target) source height node

/-- The actual copied rows preserve the edge invariant before interning. -/
theorem construct_valid (encode : Nat × Nat → Nat) (lookup : Nat → List (EnumerationState.Edge Symbol Guard))
    (source : Nat → List (EnumerationState.Edge Symbol Guard))
    (valid : ∀ node edge, edge ∈ source node → ValidEdge edge) (height node : Nat)
    (edge : EnumerationState.Edge Symbol Guard) (member : edge ∈ construct encode lookup source height node) : ValidEdge edge := by
  cases height with
  | zero => simp [construct] at member
  | succ remaining =>
      obtain ⟨original, filtered, rfl⟩ := List.mem_map.mp member
      exact EnumerationConstructors.setChildren_valid original _ (by simp)
        (valid node original (List.mem_filter.mp (List.mem_filter.mp filtered).1).1)

/-- Shared identity readback derives exact copied rows without an injectivity premise. -/
noncomputable def normalized (source : Nat → List (EnumerationState.Edge Symbol Guard))
    (target : Graph Symbol Guard) (encode : Nat × Nat → Nat) (readback : Readback source target encode)
    (meaning : Guard → Term Symbol → Prop) :
    NormalizedRows (BoundDepth.bound (fun node => (source node).map (EnumerationLanguage.edgeView meaning)))
      (EnumerationLanguage.automaton target meaning) encode where
  keep _ edge := edge.children.all fun child => !(nodeRows target (encode child)).isEmpty
  members key edge := by
    obtain ⟨height, node⟩ := key
    rw [automaton_rows]
    constructor
    · intro member
      obtain ⟨bounded, listed, rfl⟩ := List.mem_map.mp member
      have present := (readback height node bounded).mp listed
      cases height with
      | zero => simp [construct] at present
      | succ remaining =>
          obtain ⟨original, filtered, rfl⟩ := List.mem_map.mp present
          obtain ⟨sourceFiltered, childrenKept⟩ := List.mem_filter.mp filtered
          obtain ⟨present, shallow⟩ := List.mem_filter.mp sourceFiltered
          refine ⟨BoundDepth.copyEdge remaining (EnumerationLanguage.edgeView meaning original), ?_, ?_,
            EnumerationBoundedRows.copy_view _ _ _ _⟩
          · exact List.mem_map.mpr ⟨EnumerationLanguage.edgeView meaning original,
              List.mem_filter.mpr ⟨List.mem_map.mpr ⟨original, present, rfl⟩, shallow⟩, rfl⟩
          · simpa [BoundDepth.copyEdge, EnumerationLanguage.edgeView, List.all_map, Function.comp_def] using childrenKept
    · rintro ⟨original, present, kept, rfl⟩
      cases height with
      | zero => simp [BoundDepth.bound] at present
      | succ remaining =>
          obtain ⟨base, filtered, rfl⟩ := List.mem_map.mp present
          obtain ⟨mapped, shallow⟩ := List.mem_filter.mp filtered
          obtain ⟨edge, member, rfl⟩ := List.mem_map.mp mapped
          rw [← EnumerationBoundedRows.copy_view]
          apply List.mem_map.mpr
          refine ⟨EnumerationBoundedRows.copyEdge encode remaining edge, ?_, rfl⟩
          apply (readback _ _ _).mpr
          apply List.mem_map.mpr
          refine ⟨edge, List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨member, shallow⟩, ?_⟩, rfl⟩
          simpa [BoundDepth.copyEdge, EnumerationLanguage.edgeView, List.all_map, Function.comp_def] using kept
  rejected _ edge _ rejected := by
    have empty : ∃ child ∈ edge.children, nodeRows target (encode child) = [] := by simpa using rejected
    obtain ⟨child, member, absent⟩ := empty
    exact Or.inr ⟨child, member, by simp [automaton_rows, absent]⟩

/-- Interning may merge memo results without adding or removing a bounded finite term. -/
theorem accepted_exact (source : Nat → List (EnumerationState.Edge Symbol Guard)) (target : Graph Symbol Guard)
    (encode : Nat × Nat → Nat) (readback : Readback source target encode) (complete : CompleteGraph target)
    (meaning : Guard → Term Symbol → Prop) (height node : Nat) (term : Term Symbol) :
    Accepted target meaning (encode (height, node)) term ↔
      Accepts (fun state => (source state).map (EnumerationLanguage.edgeView meaning)) node term ∧ term.height ≤ height := by
  rw [EnumerationLanguage.accepted_iff _ _ complete]
  exact (normalizedRows_exact _ _ _ (normalized source target encode readback meaning) (height, node) term).trans
    (BoundDepth.bound_exact _ height node term)

/-- The actual driver retains exact bounded support with shared runtime identities. -/
theorem runs_exact [DecidableEq Symbol] (source : Nat → List (EnumerationState.Edge Symbol Guard))
    (target : Graph Symbol Guard) (encode : Nat × Nat → Nat) (readback : Readback source target encode)
    (complete : CompleteGraph target) (meaning : Guard → Term Symbol → Prop)
    (intersection : EnumerationIntersection.HashRows (EnumerationLanguage.automaton target meaning) target.intersect)
    (marker : Symbol) (height node : Nat) (term : Term Symbol) :
    (Accepts (fun state => (source state).map (EnumerationLanguage.edgeView meaning)) node term ∧ term.height ≤ height) ↔
      ∃ fuel pending after, .ok ((term, pending), after) ∈ runs target marker fuel (encode (height, node)) ∧
        ∀ obligation ∈ pending, meaning obligation.1 obligation.2 := by
  rw [← accepted_exact source target encode readback complete meaning height node term]
  exact EnumerationExact.runs_exact target meaning complete
    (EnumerationIntersection.intersection_correct target meaning complete intersection) marker _ term

end MicroCFTA.EnumerationSharedRows
