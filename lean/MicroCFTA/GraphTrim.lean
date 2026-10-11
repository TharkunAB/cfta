import MicroCFTA.Productivity
import MicroCFTA.FTAValidation

/-!
# Trimming a finite constrained graph

The source computes structural productivity without interpreting guards.
It removes transitions with unproductive children, then keeps states reachable
from the initial state. The guards on retained transitions are unchanged.
-/
namespace MicroCFTA.GraphTrim
open Language Productivity

/-- The source's live table after its structural productivity fixed point. -/
def live (states : List State) (automaton : Automaton State Symbol) : Automaton State Symbol :=
  fun state => if productive states automaton state then
    (automaton state).filter fun edge => edge.children.all (productive states automaton)
  else []

/-- Live-table construction only removes transitions. -/
theorem live_subset (states : List State) (automaton : Automaton State Symbol)
    (state : State) (edge : Edge State Symbol) (present : edge ∈ live states automaton state) :
    edge ∈ automaton state := by
  unfold live at present
  split at present
  · exact (List.mem_filter.mp present).1
  · simp at present

/-- Every accepted source term survives the structural productivity filter. -/
theorem live_complete (states : List State) (complete : ∀ state, state ∈ states)
    (automaton : Automaton State Symbol) {state : State} {term : Term Symbol}
    (accepted : Accepts automaton state term) : Accepts (live states automaton) state term := by
  induction accepted using Accepts.rec
    (motive_2 := fun childStates terms _ =>
      All₂ (Accepts (live states automaton)) childStates terms ∧ childStates.all (productive states automaton) = true) with
  | @node state edge terms member runs guard ih =>
    have marked : productive states automaton state = true :=
      (productive_correct states complete automaton state).mpr
        ⟨_, eraseGuards_accepts automaton (.node edge terms member runs guard)⟩
    exact .node edge terms (by simp [live, marked, member, ih.2]) ih.1 guard
  | nil => exact ⟨.nil, rfl⟩
  | @cons childState term childStates terms run runs ih ihs =>
    have marked : productive states automaton childState = true :=
      (productive_correct states complete automaton childState).mpr ⟨term, eraseGuards_accepts automaton run⟩
    exact ⟨.cons ih ihs.1, by simp [marked, ihs.2]⟩

/-- Structural productivity filtering preserves every constrained state language. -/
theorem live_exact (states : List State) (complete : ∀ state, state ∈ states)
    (automaton : Automaton State Symbol) (state : State) (term : Term Symbol) :
    Accepts (live states automaton) state term ↔ Accepts automaton state term :=
  ⟨FTAValidation.accepts_transfer _ _ (live_subset states automaton), live_complete states complete automaton⟩

/-- Keep precisely the live-table states reachable from the initial state. -/
def trim [DecidableEq State] (states : List State) (automaton : Automaton State Symbol)
    (root : State) : Automaton State Symbol := fun state =>
  if reachClosure states (successors (live states automaton)) [root] state then live states automaton state else []

/-- Trimming only removes source transitions. -/
theorem trim_subset [DecidableEq State] (states : List State) (automaton : Automaton State Symbol)
    (root state : State) (edge : Edge State Symbol) (present : edge ∈ trim states automaton root state) :
    edge ∈ automaton state := by
  unfold trim at present
  split at present
  · exact live_subset states automaton state edge present
  · simp at present

/-- Every run from a reachable live state survives the reachability filter. -/
theorem reachable_complete [DecidableEq State] (states : List State) (complete : ∀ state, state ∈ states)
    (automaton : Automaton State Symbol) (root : State) {state : State} {term : Term Symbol}
    (accepted : Accepts (live states automaton) state term) :
    Reachable (successors (live states automaton)) [root] state → Accepts (trim states automaton root) state term := by
  induction accepted using Accepts.rec
    (motive_2 := fun childStates terms _ =>
      (∀ state ∈ childStates, Reachable (successors (live states automaton)) [root] state) →
        All₂ (Accepts (trim states automaton root)) childStates terms) with
  | @node state edge terms member runs guard ih =>
    intro reached
    have marked := (reachClosure_correct states complete _ _ state).mpr reached
    exact .node edge terms (by simp [trim, marked, member])
      (ih (fun child present => reachable_child (live states automaton) [root] reached member present)) guard
  | nil => exact .nil
  | cons head tail ih ihtail =>
    rename_i reached
    exact .cons (ih (reached _ (by simp))) (ihtail (fun state member => reached state (by simp [member])))

/-- The complete trim operation preserves all and only the original root terms. -/
theorem trim_exact [DecidableEq State] (states : List State) (complete : ∀ state, state ∈ states)
    (automaton : Automaton State Symbol) (root : State) (term : Term Symbol) :
    Accepts (trim states automaton root) root term ↔ Accepts automaton root term := by
  constructor
  · exact FTAValidation.accepts_transfer _ _ (trim_subset states automaton root)
  · intro accepted
    exact reachable_complete states complete automaton root (live_complete states complete automaton accepted)
      (.seed (by simp))

/-- Equal set counts justify the source's fixed-point stopping condition. -/
theorem cardinality_stop (states : List State) (complete : ∀ state, state ∈ states)
    (before after : State → Bool) (included : Included before after)
    (same : states.countP before = states.countP after) : before = after := by
  classical
  apply Classical.byContradiction
  intro different
  have strict := count_strict_of_ne states complete before after included different
  omega

end MicroCFTA.GraphTrim
