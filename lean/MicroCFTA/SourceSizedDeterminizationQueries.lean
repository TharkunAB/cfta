import MicroCFTA.SourceSizedDeterminizationRun
import MicroCFTA.SourceSizedDeterminizationRows
import MicroCFTA.SourceSizedApiLaws
import MicroCFTA.SourceCyclicAutomaton

/-!
# Exact queries after bounded determinization

Successful concrete discovery derives the actual Left/Right row graph's
language and unambiguous classes. The existing count-table query worker
then satisfies the full signed Sized specification at each original root.
The result also holds after a permutation of each row, including row sorts.
The query order is the transformed row graph's order.

Other modules construct finite canonical inputs and ordered map/set views.
Their native Haskell correspondence and current public Sized routing remain
separate. The general closed-row composition supports those derived views.
This module does not bound total work.
-/
namespace MicroCFTA.SourceSizedDeterminizationQueries
open Language RecursiveSize
open SourceSizedDeterminizationKernel SourceSizedDeterminizationClosure
open SourceSizedDispatcher

variable {State Symbol : Type} [DecidableEq State] [DecidableEq Symbol]

private theorem plain_rows (states : List State) (source : Automaton State Symbol)
    (choices : List (Choice State Symbol)) :
    Decoder.Plain (SourceSizedDeterminizationRows.rows states source choices) := by
  intro state edge member term
  cases state <;> (obtain ⟨choice, _, rfl⟩ := List.mem_map.mp member; rfl)

/-- Concrete bounded discovery derives the original language at every actual Left root. -/
theorem rows_language (limit : Nat) (states : List State) (source : Automaton State Symbol)
    (plain : Decoder.Plain source)
    (supported : ∀ state edge, edge ∈ source state → state ∈ states)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (returned : SourceSizedDeterminizationRun.compile limit states source = .ready known choices)
    (state : State) (term : Term Symbol) :
    Accepts (SourceSizedDeterminizationRows.rows states source choices) (.inl state) term ↔
      Accepts source state term :=
  SourceSizedDeterminizationRows.left_accepts_iff states source plain supported known choices
    (SourceSizedDeterminizationRun.compile_closed limit states source known choices returned) state term

/-- Concrete discovery supplies uniqueness for the full graph, including all original roots. -/
theorem rows_unique (limit : Nat) (states : List State) (source : Automaton State Symbol)
    (plain : Decoder.Plain source)
    (supported : ∀ state edge, edge ∈ source state → state ∈ states)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (returned : SourceSizedDeterminizationRun.compile limit states source = .ready known choices) :
    SizedRank.Unambiguous (SourceSizedDeterminizationRows.rows states source choices) :=
  SourceSizedDeterminizationRows.classes_unique states source plain supported choices
    (SourceSizedDeterminizationRun.compile_closed limit states source known choices returned).distinct

/-- A successful transformed count table gives all signed query laws at the original language. -/
theorem queries_exact (limit : Nat) (states : List State) (source : Automaton State Symbol)
    (plain : Decoder.Plain source)
    (supported : ∀ state edge, edge ∈ source state → state ∈ states)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (returned : SourceSizedDeterminizationRun.compile limit states source = .ready known choices)
    (root : State) :
    SourceSizedApiLaws.Exact
      (optimizedApi (SourceSizedDeterminizationRows.rows states source choices) (.inl root))
      (Accepts source root) := by
  rw [optimizedApi_of_unique _ (plain_rows states source choices)
    (rows_unique limit states source plain supported known choices returned)]
  exact SourceSizedApiLaws.reference _ _ _
    (rows_language limit states source plain supported known choices returned root)

private theorem permuted_unique (states : List State) (source : Automaton State Symbol)
    (plain : Decoder.Plain source)
    (supported : ∀ state edge, edge ∈ source state → state ∈ states)
    (choices : List (Choice State Symbol)) (distinct : choices.Nodup)
    (ordered : Automaton (Sum State (List State)) Symbol)
    (permutation : ∀ state,
      (ordered state).Perm (SourceSizedDeterminizationRows.rows states source choices state)) :
    SizedRank.Unambiguous ordered := by
  have language := SourceCyclicAutomaton.permutation_language
    (SourceSizedDeterminizationRows.rows states source choices) ordered permutation
  have edgeTransfer (edge : Edge (Sum State (List State)) Symbol) (term : Term Symbol)
      (accepted : AutomatonAmbiguity.EdgeLanguage (Accepts ordered) edge term) :
      AutomatonAmbiguity.EdgeLanguage
        (Accepts (SourceSizedDeterminizationRows.rows states source choices)) edge term := by
    obtain ⟨terms, same, children, guard⟩ := accepted
    exact ⟨terms, same, children.imp (fun state term run => (language state term).mp run), guard⟩
  have disjoint (state : Sum State (List State)) : RecursiveUnambiguous.DisjointRows ordered state := by
    let separates := fun first second : Edge (Sum State (List State)) Symbol =>
      ∀ term, AutomatonAmbiguity.EdgeLanguage (Accepts ordered) first term →
        ¬AutomatonAmbiguity.EdgeLanguage (Accepts ordered) second term
    have original : (SourceSizedDeterminizationRows.rows states source choices state).Pairwise separates :=
      (SourceSizedDeterminizationRows.rows_disjoint states source plain supported choices distinct state).imp
        (by
          intro first second different term left right
          exact different term (edgeTransfer first term left) (edgeTransfer second term right))
    have symmetric : ∀ {first second}, separates first second → separates second first := by
      intro first second different term left right
      exact different term right left
    exact ((permutation state).pairwise_iff symmetric).mpr original
  have plainOutput : Decoder.Plain ordered := by
    intro state edge member term
    exact plain_rows states source choices state edge ((permutation state).mem_iff.mp member) term
  intro state size
  exact RecursiveUnambiguous.enumerate_nodup ordered plainOutput (fun _ => True) (by simp)
    (fun state _ => disjoint state) size state trivial

/-- Derived closed rows give exact optimized queries after a concrete row permutation. -/
theorem closed_ordered_queries_exact (states : List State) (source : Automaton State Symbol)
    (plain : Decoder.Plain source)
    (supported : ∀ state edge, edge ∈ source state → state ∈ states)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (closed : Closed states source known choices)
    (ordered : Automaton (Sum State (List State)) Symbol)
    (permutation : ∀ state,
      (ordered state).Perm (SourceSizedDeterminizationRows.rows states source choices state))
    (root : State) :
    SourceSizedApiLaws.Exact (optimizedApi ordered (.inl root)) (Accepts source root) := by
  have plainOutput : Decoder.Plain ordered := by
    intro state edge member term
    exact plain_rows states source choices state edge ((permutation state).mem_iff.mp member) term
  rw [optimizedApi_of_unique ordered plainOutput
    (permuted_unique states source plain supported choices closed.distinct ordered permutation)]
  apply SourceSizedApiLaws.reference
  intro term
  exact (SourceCyclicAutomaton.permutation_language _ ordered permutation (.inl root) term).trans
    (SourceSizedDeterminizationRows.left_accepts_iff states source plain supported known choices closed root term)

/-- Row sorting preserves exact counts and inverse ranks in the resulting transformed order. -/
theorem ordered_queries_exact (limit : Nat) (states : List State) (source : Automaton State Symbol)
    (plain : Decoder.Plain source)
    (supported : ∀ state edge, edge ∈ source state → state ∈ states)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (returned : SourceSizedDeterminizationRun.compile limit states source = .ready known choices)
    (ordered : Automaton (Sum State (List State)) Symbol)
    (permutation : ∀ state,
      (ordered state).Perm (SourceSizedDeterminizationRows.rows states source choices state))
    (root : State) :
    SourceSizedApiLaws.Exact (optimizedApi ordered (.inl root)) (Accepts source root) :=
  closed_ordered_queries_exact states source plain supported known choices
    (SourceSizedDeterminizationRun.compile_closed limit states source known choices returned)
    ordered permutation root

end MicroCFTA.SourceSizedDeterminizationQueries
