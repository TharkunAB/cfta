import MicroCFTA.EnumerationCPSState
import MicroCFTA.EnumerationExact

/-!
# Public runs through the CPS interface

The public composition keeps enumeration, term rendering, state reads, and
ordered obligation rendering separate. The established finite workers enter
through the proved monad translation. All model errors remain visible.
Successful support transfers from `EnumerationExact`; it still requires the
same complete-graph and intersection contracts. This is an algebraic backend
bridge, not verified extraction of Haskell or an infinite productivity proof.
-/

namespace MicroCFTA.EnumerationCPSRuns

open Language Fragments EnumerationCPSChecked EnumerationCPSState

variable {Symbol Guard : Type}

local instance : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

/-- The current public runner composed through the checked CPS operations. -/
def action (graph : EnumerationState.Graph Symbol Guard) (marker : Symbol) (fuel : Nat) :
    Action Symbol Guard (Term Symbol × List (Guard × Term Symbol)) :=
  bind (lift (EnumerationState.enumerateFully graph (fun _ _ => none) EnumerationState.noPruning fuel ())) fun _ =>
    bind (lift (EnumerationState.expandUVar graph marker fuel 0)) fun term =>
      bind get fun state =>
        bind (EnumerationCPSState.mapM (fun obligation =>
          bind (lift (EnumerationState.expandFragment graph marker fuel obligation.2)) fun subtree =>
            EnumerationCPSChecked.pure (obligation.1, subtree)) state.obligations) fun pending =>
          EnumerationCPSChecked.pure (term, pending)

/-- The same existing public action before applying its initial state. -/
def model (graph : EnumerationState.Graph Symbol Guard) (marker : Symbol) (fuel : Nat) :
    EnumerationState.EnumerateM Symbol Guard (Term Symbol × List (Guard × Term Symbol)) := do
  EnumerationState.enumerateFully graph (fun _ _ => none) EnumerationState.noPruning fuel ()
  let term ← EnumerationState.expandUVar graph marker fuel 0
  let pending ← (← (MonadStateOf.get : EnumerationState.EnumerateM Symbol Guard (EnumerationState.State Symbol Guard))).obligations.mapM fun (guard, fragment) => do
    Pure.pure (guard, ← EnumerationState.expandFragment graph marker fuel fragment)
  Pure.pure (term, pending)

/-- Each public composition step preserves the entire ordered state/error list. -/
theorem action_exact (graph : EnumerationState.Graph Symbol Guard) (marker : Symbol) (fuel : Nat) :
    Represents (action graph marker fuel) (model graph marker fuel) := by
  unfold action model
  apply bind_exact _ _ _ _ (lift_exact _)
  intro _
  apply bind_exact _ _ _ _ (lift_exact _)
  intro term
  apply bind_exact _ _ _ _ get_exact
  intro state
  apply bind_exact _ _ _ _ (mapM_exact _ _ (fun obligation => ?_) state.obligations)
  · intro pending
    exact pure_exact (term, pending)
  · exact bind_exact _ _ _ _ (lift_exact _) (fun subtree => pure_exact (obligation.1, subtree))

/-- The checked public runner uses exactly the source all-branches continuations. -/
def runs (graph : EnumerationState.Graph Symbol Guard) (marker : Symbol) (fuel root : Nat) :=
  allResults (action graph marker fuel) (EnumerationState.initial root)

/-- CPS runs preserve all established model results, including their order and multiplicity. -/
theorem runs_eq (graph : EnumerationState.Graph Symbol Guard) (marker : Symbol) (fuel root : Nat) :
    runs graph marker fuel root = EnumerationState.runs graph marker fuel root := by
  unfold runs
  rw [allResults_exact _ _ (action_exact graph marker fuel)]
  rfl

/-- A successful public CPS run has exactly the existing checked finite-term semantics. -/
theorem runs_exact (graph : EnumerationState.Graph Symbol Guard) (meaning : Guard → Term Symbol → Prop)
    (complete : EnumerationSemantics.CompleteGraph graph)
    (correct : EnumerationCorrectness.IntersectionCorrect graph (EnumerationCorrectness.Accepted graph meaning))
    (marker : Symbol) (root : Nat) (term : Term Symbol) :
    EnumerationCorrectness.Accepted graph meaning root term ↔
      ∃ fuel pending after, .ok ((term, pending), after) ∈ runs graph marker fuel root ∧
        ∀ obligation ∈ pending, meaning obligation.1 obligation.2 := by
  simp only [runs_eq]
  exact EnumerationExact.runs_exact graph meaning complete correct marker root term

/-- The successful projection retains final states and residual obligations. -/
def successfulRuns (graph : EnumerationState.Graph Symbol Guard) (marker : Symbol) (fuel root : Nat) :=
  successes (runs graph marker fuel root)

/-- Successful CPS branches have exact accepted support, without hiding a global error-free claim. -/
theorem successfulRuns_exact (graph : EnumerationState.Graph Symbol Guard) (meaning : Guard → Term Symbol → Prop)
    (complete : EnumerationSemantics.CompleteGraph graph)
    (correct : EnumerationCorrectness.IntersectionCorrect graph (EnumerationCorrectness.Accepted graph meaning))
    (marker : Symbol) (root : Nat) (term : Term Symbol) :
    EnumerationCorrectness.Accepted graph meaning root term ↔
      ∃ fuel pending after, ((term, pending), after) ∈ successfulRuns graph marker fuel root ∧
        ∀ obligation ∈ pending, meaning obligation.1 obligation.2 := by
  simp only [successfulRuns, mem_successes]
  exact runs_exact graph meaning complete correct marker root term

/-- An error-free public execution loses no result through the source-shaped projection. -/
theorem error_free_runner (graph : EnumerationState.Graph Symbol Guard) (marker : Symbol) (fuel root : Nat)
    (safe : ErrorFree (runs graph marker fuel root)) :
    (successfulRuns graph marker fuel root).map Except.ok = runs graph marker fuel root :=
  successes_recover _ safe

/-- The public source map-fst projection discards only final states. -/
def values (graph : EnumerationState.Graph Symbol Guard) (marker : Symbol) (fuel root : Nat) :=
  (successfulRuns graph marker fuel root).map Prod.fst

/-- Each public term/residual pair has an actual successful final branch state. -/
theorem values_member (graph : EnumerationState.Graph Symbol Guard) (marker : Symbol) (fuel root : Nat)
    (term : Term Symbol) (pending : List (Guard × Term Symbol)) :
    (term, pending) ∈ values graph marker fuel root ↔
      ∃ after, .ok ((term, pending), after) ∈ runs graph marker fuel root := by
  simp only [values, List.mem_map]
  constructor
  · rintro ⟨⟨result, after⟩, member, same⟩
    change result = (term, pending) at same
    subst result
    exact ⟨after, (mem_successes _ _ _).mp member⟩
  · rintro ⟨after, member⟩
    exact ⟨((term, pending), after), (mem_successes _ _ _).mpr member, rfl⟩

/-- Existing eventual completeness transfers to the CPS runner at every larger bound. -/
theorem runs_complete_eventually (graph : EnumerationState.Graph Symbol Guard)
    (meaning : Guard → Term Symbol → Prop) (complete : EnumerationSemantics.CompleteGraph graph)
    (correct : EnumerationCorrectness.IntersectionCorrect graph (EnumerationCorrectness.Accepted graph meaning))
    (marker : Symbol) (root : Nat) (term : Term Symbol)
    (accepted : EnumerationCorrectness.Accepted graph meaning root term) :
    ∃ bound pending after, (∀ fuel, bound ≤ fuel → .ok ((term, pending), after) ∈ runs graph marker fuel root) ∧
      ∀ obligation ∈ pending, meaning obligation.1 obligation.2 := by
  simp only [runs_eq]
  exact EnumerationExact.runs_complete_eventually graph meaning complete correct marker root term accepted

end MicroCFTA.EnumerationCPSRuns
