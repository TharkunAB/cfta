import MicroCFTA.SourceFiniteAutomaton
import MicroCFTA.SourceSizedDispatchGraph

/-!
# The bottom-up deterministic Sized gate

The gate compares the number of transition occurrences with the number of
distinct symbol and ordered-child keys. The list view models set cardinality.
It does not model the physical implementation or complexity of `Data.Set`.
Every stored row must occur in the finite state list. Cycles are permitted.
-/
namespace MicroCFTA.SourceSizedDeterministic
open Language RecursiveSize SizedRank

/-- A transition key retains the symbol and every ordered child state. -/
def rowKey (edge : Edge State Symbol) : Symbol × List State :=
  (edge.label, edge.children)

/-- Retain each transition occurrence and its owner state. -/
def ownedRows (rows : Automaton State Symbol) (states : List State) :
    List (State × Edge State Symbol) :=
  states.flatMap fun state => (rows state).map (Prod.mk state)

/-- The source gate counts all occurrences before it removes duplicate keys. -/
def bottomUpDeterministic [DecidableEq State] [DecidableEq Symbol]
    (rows : Automaton State Symbol) (states : List State) : Bool :=
  let keys := (ownedRows rows states).map (fun entry => rowKey entry.2)
  keys.length == keys.eraseDups.length

/-- A passing cardinality check gives distinct keys for all stored occurrences. -/
theorem gate_keys [DecidableEq State] [DecidableEq Symbol]
    (rows : Automaton State Symbol) (states : List State)
    (passed : bottomUpDeterministic rows states = true) :
    ((ownedRows rows states).map (fun entry => rowKey entry.2)).Nodup := by
  apply SourceFiniteAutomaton.distinct_count _ |>.mp
  exact (of_decide_eq_true passed).symm

private theorem key_injective (key : α → β) (entries : List α)
    (unique : (entries.map key).Nodup) (first second : α)
    (firstMember : first ∈ entries) (secondMember : second ∈ entries)
    (same : key first = key second) : first = second := by
  induction entries with
  | nil => simp at firstMember
  | cons entry rest ih =>
      simp only [List.map_cons, List.nodup_cons] at unique
      rcases List.mem_cons.mp firstMember with rfl | firstTail
      · rcases List.mem_cons.mp secondMember with rfl | secondTail
        · rfl
        · exact False.elim (unique.1 (List.mem_map.mpr ⟨second, secondTail, same.symm⟩))
      · rcases List.mem_cons.mp secondMember with rfl | secondTail
        · exact False.elim (unique.1 (List.mem_map.mpr ⟨first, firstTail, same⟩))
        · exact ih unique.2 firstTail secondTail

private theorem owned_member (rows : Automaton State Symbol) (states : List State)
    (support : ∀ state edge, edge ∈ rows state → state ∈ states)
    (state : State) (edge : Edge State Symbol) (member : edge ∈ rows state) :
    (state, edge) ∈ ownedRows rows states :=
  List.mem_flatMap.mpr ⟨state, support state edge member,
    List.mem_map.mpr ⟨edge, member, rfl⟩⟩

/-- A finite term reaches at most one state after the global key check passes. -/
theorem accepted_state_unique [DecidableEq State] [DecidableEq Symbol]
    (rows : Automaton State Symbol) (states : List State)
    (support : ∀ state edge, edge ∈ rows state → state ∈ states)
    (passed : bottomUpDeterministic rows states = true) (term : Term Symbol)
    (first second : State) (left : Accepts rows first term) (right : Accepts rows second term) :
    first = second := by
  have unique := gate_keys rows states passed
  have result := Term.rec
    (motive_1 := fun term => ∀ first second, Accepts rows first term → Accepts rows second term → first = second)
    (motive_2 := fun terms => ∀ first second, All₂ (Accepts rows) first terms →
      All₂ (Accepts rows) second terms → first = second) ?_ ?_ ?_ term
  · exact result first second left right
  · intro symbol children ih first second left right
    obtain ⟨a, aMember, aLabel, aRuns, _⟩ := (accepts_node_iff rows first symbol children).mp left
    obtain ⟨b, bMember, bLabel, bRuns, _⟩ := (accepts_node_iff rows second symbol children).mp right
    have same : rowKey a = rowKey b := Prod.ext (aLabel.trans bLabel.symm) (ih _ _ aRuns bRuns)
    have owners := key_injective (fun entry : State × Edge State Symbol => rowKey entry.2)
      (ownedRows rows states) unique (first, a) (second, b)
      (owned_member rows states support first a aMember)
      (owned_member rows states support second b bMember) same
    exact congrArg Prod.fst owners
  · intro first second left right
    cases left
    cases right
    rfl
  · intro child children head tail first second left right
    cases left with
    | cons leftHead leftTail =>
      cases right with
      | cons rightHead rightTail =>
        rw [head _ _ leftHead rightHead, tail _ _ leftTail rightTail]

private theorem children_unique [DecidableEq State] [DecidableEq Symbol]
    (rows : Automaton State Symbol) (states : List State)
    (support : ∀ state edge, edge ∈ rows state → state ∈ states)
    (passed : bottomUpDeterministic rows states = true)
    (terms : List (Term Symbol)) (first second : List State)
    (left : All₂ (Accepts rows) first terms) (right : All₂ (Accepts rows) second terms) :
    first = second := by
  induction left generalizing second with
  | nil => cases right; rfl
  | @cons a term rest terms accepted runs ih =>
      cases right with
      | cons acceptedRight runsRight =>
        rw [accepted_state_unique rows states support passed term _ _ accepted acceptedRight, ih _ runsRight]

/-- A passing key check separates the languages of all row occurrences. -/
theorem gate_disjoint [DecidableEq State] [DecidableEq Symbol]
    (rows : Automaton State Symbol) (states : List State)
    (support : ∀ state edge, edge ∈ rows state → state ∈ states)
    (passed : bottomUpDeterministic rows states = true) (state : State) :
    RecursiveUnambiguous.DisjointRows rows state := by
  have global := gate_keys rows states passed
  have flattened : (states.flatMap fun state => (rows state).map rowKey).Nodup := by
    simpa only [ownedRows, List.map_flatMap, List.map_map, Function.comp_def] using global
  by_cases inside : state ∈ states
  · have localKeys := (List.pairwise_flatMap.mp flattened).1 state inside
    apply (List.pairwise_map.mp localKeys).imp
    intro first second different term left right
    obtain ⟨leftTerms, leftEq, leftRuns, _⟩ := left
    obtain ⟨rightTerms, rightEq, rightRuns, _⟩ := right
    obtain ⟨sameLabel, sameTerms⟩ := Term.node.inj (leftEq.symm.trans rightEq)
    rw [← sameTerms] at rightRuns
    exact different (Prod.ext sameLabel (children_unique rows states support passed _ _ _ leftRuns rightRuns))
  · have empty : rows state = [] := List.eq_nil_iff_forall_not_mem.mpr (by
      intro edge member
      exact inside (support state edge member))
    simp [RecursiveUnambiguous.DisjointRows, empty]

/-- The executable key gate derives distinct terms in every size class. -/
theorem gate_unique [DecidableEq State] [DecidableEq Symbol]
    (rows : Automaton State Symbol) (plain : Decoder.Plain rows)
    (states : List State) (support : ∀ state edge, edge ∈ rows state → state ∈ states)
    (passed : bottomUpDeterministic rows states = true) : SizedRank.Unambiguous rows := by
  intro state size
  exact RecursiveUnambiguous.enumerate_nodup rows plain (fun _ => True) (by simp)
    (fun state _ => gate_disjoint rows states support passed state) size state trivial

end MicroCFTA.SourceSizedDeterministic
