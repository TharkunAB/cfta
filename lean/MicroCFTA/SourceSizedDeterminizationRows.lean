import MicroCFTA.SourceSizedDeterminizationClosure
import MicroCFTA.SymbolicGraphView

/-!
# Original roots and deterministic subset rows

The source returns Left roots and Right subset states. Each original root
retains every emitted transition whose target contains that original state.
All children use Right keys. This file proves language and class uniqueness.
Ordered map and set readback and the final row sort remain separate.
-/
namespace MicroCFTA.SourceSizedDeterminizationRows
open Language SourceSizedDeterminizationKernel
open SourceSizedDeterminizationClosure

variable {State Symbol : Type} [DecidableEq State] [DecidableEq Symbol]

/-- An emitted transition wraps each child subset as a Right state. -/
def wrap (choice : Choice State Symbol) : Edge (Sum State (List State)) Symbol :=
  ⟨choice.1, choice.2.map Sum.inr, fun _ => true⟩

/-- Read original roots and deterministic keys from the same emitted choices. -/
def rows (states : List State) (source : Automaton State Symbol)
    (choices : List (Choice State Symbol)) : Automaton (Sum State (List State)) Symbol
  | .inl state => (choices.filter fun choice =>
      decide (state ∈ target states source choice.1 choice.2)).map wrap
  | .inr key => (choices.filter fun choice =>
      decide (target states source choice.1 choice.2 = key)).map wrap

/-- Right rows replace only the child keys of the kernel's emitted rows. -/
theorem right_rows_correspond (states : List State) (source : Automaton State Symbol)
    (choices : List (Choice State Symbol)) :
    SymbolicGraphView.RowsCorrespond (emittedRows states source choices)
      (rows states source choices) Sum.inr := by
  intro key edge
  constructor
  · intro member
    obtain ⟨choice, present, rfl⟩ := List.mem_map.mp member
    exact ⟨⟨choice.1, choice.2, fun _ => true⟩, List.mem_map.mpr ⟨choice, present, rfl⟩, rfl⟩
  · rintro ⟨original, present, rfl⟩
    obtain ⟨choice, selected, rfl⟩ := List.mem_map.mp present
    exact List.mem_map.mpr ⟨choice, selected, rfl⟩

/-- A Right state accepts exactly its kernel subset language. -/
theorem right_accepts_iff (states : List State) (source : Automaton State Symbol)
    (choices : List (Choice State Symbol)) (key : List State) (term : Term Symbol) :
    Accepts (rows states source choices) (.inr key) term ↔
      Accepts (emittedRows states source choices) key term :=
  SymbolicGraphView.rowsCorrespond_exact _ _ _
    (right_rows_correspond states source choices) key term

private theorem right_runs_iff (states : List State) (source : Automaton State Symbol)
    (choices : List (Choice State Symbol)) (keys : List (List State)) (terms : List (Term Symbol)) :
    All₂ (Accepts (rows states source choices)) (keys.map Sum.inr) terms ↔
      All₂ (Accepts (emittedRows states source choices)) keys terms := by
  rw [SymbolicGraphView.all₂_map_iff]
  constructor
  · exact All₂.imp (fun key term run => (right_accepts_iff states source choices key term).mp run)
  · exact All₂.imp (fun key term run => (right_accepts_iff states source choices key term).mpr run)

/-- A Left root accepts the union of the subset languages that contain it. -/
theorem left_targets_iff (states : List State) (source : Automaton State Symbol)
    (choices : List (Choice State Symbol)) (state : State) (term : Term Symbol) :
    Accepts (rows states source choices) (.inl state) term ↔
      ∃ key, state ∈ key ∧ Accepts (emittedRows states source choices) key term := by
  cases term with
  | node symbol terms =>
      constructor
      · intro accepted
        obtain ⟨edge, member, label, children, _⟩ :=
          (accepts_node_iff (rows states source choices) (.inl state) symbol terms).mp accepted
        obtain ⟨choice, selected, rfl⟩ := List.mem_map.mp member
        have present := List.mem_filter.mp selected
        have emitted : (⟨choice.1, choice.2, fun _ => true⟩ : Edge (List State) Symbol) ∈
            emittedRows states source choices (target states source choice.1 choice.2) :=
          List.mem_map.mpr ⟨choice, List.mem_filter.mpr ⟨present.1, by simp⟩, rfl⟩
        refine ⟨_, of_decide_eq_true present.2, ?_⟩
        exact (accepts_node_iff _ _ _ _).mpr
          ⟨_, emitted, label, (right_runs_iff states source choices choice.2 terms).mp children, rfl⟩
      · rintro ⟨key, inside, accepted⟩
        obtain ⟨edge, member, label, children, _⟩ :=
          (accepts_node_iff (emittedRows states source choices) key symbol terms).mp accepted
        obtain ⟨choice, selected, rfl⟩ := List.mem_map.mp member
        have present := List.mem_filter.mp selected
        have owner : state ∈ target states source choice.1 choice.2 := by
          rw [of_decide_eq_true present.2]
          exact inside
        have emitted : wrap choice ∈ rows states source choices (.inl state) :=
          List.mem_map.mpr ⟨choice, List.mem_filter.mpr ⟨present.1, decide_eq_true owner⟩, rfl⟩
        exact (accepts_node_iff _ _ _ _).mpr
          ⟨_, emitted, label, (right_runs_iff states source choices choice.2 terms).mpr children, rfl⟩

/-- Closed discovery gives the original language at each actual Left root. -/
theorem left_accepts_iff (states : List State) (source : Automaton State Symbol)
    (plain : Decoder.Plain source)
    (supported : ∀ state edge, edge ∈ source state → state ∈ states)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (closed : Closed states source known choices) (state : State) (term : Term Symbol) :
    Accepts (rows states source choices) (.inl state) term ↔ Accepts source state term := by
  rw [left_targets_iff]
  constructor
  · rintro ⟨key, member, accepted⟩
    exact (SourceSizedDeterminizationKernel.accepted_exact
      states source plain supported choices term key accepted state).mp member
  · intro accepted
    obtain ⟨key, _, member, run⟩ := SourceSizedDeterminizationClosure.accepted_complete
      states source plain supported known choices closed term state accepted
    exact ⟨key, member, run⟩

private theorem right_child_keys_unique (states : List State) (source : Automaton State Symbol)
    (plain : Decoder.Plain source)
    (supported : ∀ state edge, edge ∈ source state → state ∈ states)
    (choices : List (Choice State Symbol)) (terms : List (Term Symbol))
    (first second : List (List State))
    (left : All₂ (Accepts (rows states source choices)) (first.map Sum.inr) terms)
    (right : All₂ (Accepts (rows states source choices)) (second.map Sum.inr) terms) : first = second := by
  have leftRuns := (right_runs_iff states source choices first terms).mp left
  have rightRuns := (right_runs_iff states source choices second terms).mp right
  clear left right
  induction leftRuns generalizing second with
  | nil => cases rightRuns; rfl
  | cons accepted rest ih =>
      cases rightRuns with
      | cons other others =>
          rw [SourceSizedDeterminizationKernel.accepted_unique
            states source plain supported choices _ _ _ accepted other, ih _ others]

/-- Distinct token and child-key choices give disjoint Left and Right alternatives. -/
theorem rows_disjoint (states : List State) (source : Automaton State Symbol)
    (plain : Decoder.Plain source)
    (supported : ∀ state edge, edge ∈ source state → state ∈ states)
    (choices : List (Choice State Symbol)) (distinct : choices.Nodup)
    (state : Sum State (List State)) :
    RecursiveUnambiguous.DisjointRows (rows states source choices) state := by
  unfold RecursiveUnambiguous.DisjointRows
  cases state <;> simp only [rows]
  all_goals
    apply List.pairwise_map.mpr
    apply (distinct.filter _).imp
    intro first second different term left right
    obtain ⟨leftTerms, leftEq, leftRuns, _⟩ := left
    obtain ⟨rightTerms, rightEq, rightRuns, _⟩ := right
    obtain ⟨sameLabel, sameTerms⟩ := Term.node.inj (leftEq.symm.trans rightEq)
    rw [← sameTerms] at rightRuns
    exact different (Prod.ext sameLabel
      (right_child_keys_unique states source plain supported choices _ _ _ leftRuns rightRuns))

/-- Every exact size class is unique on the full Left and Right state graph. -/
theorem classes_unique (states : List State) (source : Automaton State Symbol)
    (plain : Decoder.Plain source)
    (supported : ∀ state edge, edge ∈ source state → state ∈ states)
    (choices : List (Choice State Symbol)) (distinct : choices.Nodup) :
    SizedRank.Unambiguous (rows states source choices) := by
  have plainOutput : Decoder.Plain (rows states source choices) := by
    intro state edge member term
    cases state <;>
      (obtain ⟨choice, _, rfl⟩ := List.mem_map.mp member; rfl)
  intro state size
  exact RecursiveUnambiguous.enumerate_nodup _ plainOutput (fun _ => True) (by simp)
    (fun state _ => rows_disjoint states source plain supported choices distinct state) size state trivial

end MicroCFTA.SourceSizedDeterminizationRows
