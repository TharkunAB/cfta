import MicroCFTA.BinderTermination

/-!
# Cycle detection supplies the binder construction rank

The number of reachable active states strictly decreases along an edge from
a state that is not on a cycle. Thus a cycle detector needs only to mark every
actual active cycle to ensure that optional binder construction terminates.
Additional marked states are harmless.
-/

namespace MicroCFTA.BinderSchedule
open Language Binding BinderLanguage BinderGraph BinderCompile Productivity

/-- Successors in the source's induced graph of still active states. -/
def activeNext (graph : Automaton Nat Symbol) (active : List Nat) (state : Nat) : List Nat :=
  if state ∈ active then (successors graph state).filter (fun child => decide (child ∈ active)) else []

/-- A nonempty cycle takes one edge and then returns by a finite path. -/
def OnCycle (graph : Automaton Nat Symbol) (active : List Nat) (state : Nat) : Prop :=
  ∃ child ∈ activeNext graph active state, Reachable (activeNext graph active) [child] state

/-- The source cycle set must include every state on a cycle in the current induced graph. -/
def CycleComplete (graph : Automaton Nat Symbol) (cyclic : List Nat → Nat → Bool) : Prop :=
  ∀ active state, OnCycle graph active state → cyclic active state = true

/-- Compose two finite reachability paths in an arbitrary graph. -/
theorem reach_compose (next : Nat → List Nat) (first middle last : Nat)
    (left : Reachable next [first] middle) (right : Reachable next [middle] last) :
    Reachable next [first] last := by
  induction right with
  | seed present => simpa using (List.mem_singleton.mp present) ▸ left
  | step _ member ih => exact .step ih member

/-- Count distinct listed positions that are structurally reachable in the active graph. -/
noncomputable def reachRank (graph : Automaton Nat Symbol) (active : List Nat) (state : Nat) : Nat :=
  active.countP (fun target => @decide (Reachable (activeNext graph active) [state] target) (Classical.propDecidable _))

/-- A cycle-complete selector supplies the structural decrease required by construction. -/
theorem cycle_ranked (graph : Automaton Nat Symbol) (cyclic : List Nat → Nat → Bool)
    (complete : CycleComplete graph cyclic) : Ranked graph cyclic (reachRank graph) := by
  classical
  intro active state present unmarked edge member child belongs inside
  have step : child ∈ activeNext graph active state := by
    simp only [activeNext, ite_eq_left present, List.mem_filter, decide_eq_true_eq]
    exact ⟨List.mem_flatMap.mpr ⟨edge, member, belongs⟩, inside⟩
  have down : Reachable (activeNext graph active) [state] child := .step (.seed (by simp)) step
  have cannotReturn : ¬Reachable (activeNext graph active) [child] state := by
    intro returned
    have marked := complete active state ⟨child, step, returned⟩
    simp [unmarked] at marked
  apply count_strict
  · intro target _ reached
    apply decide_eq_true
    exact reach_compose _ state child target down (of_decide_eq_true reached)
  · refine ⟨state, present, ?_, ?_⟩
    · exact decide_eq_false cannotReturn
    · exact decide_eq_true (.seed (by simp))

/-- Marking every actual cycle is sufficient for total stable binder construction. -/
theorem cycles_build_eventual (graph : Automaton Nat Symbol) (cyclic : List Nat → Nat → Bool)
    (complete : CycleComplete graph cyclic) (active : List Nat) (state : Nat) :
    Eventually (fun fuel => build graph cyclic fuel active state) :=
  build_eventual graph cyclic (reachRank graph) (cycle_ranked graph cyclic complete) active state

/-- The full finite-graph conversion is total and exact under the cycle detector's graph contract. -/
theorem cycles_closed_total (graph : Automaton Nat Symbol) (cyclic : List Nat → Nat → Bool)
    (complete : CycleComplete graph cyclic) (states : List Nat) (unique : states.Nodup)
    (closed : Closed graph states) (root : Nat) (present : root ∈ states) :
    ∃ bound shape, (∀ fuel, bound ≤ fuel → build graph cyclic fuel states root = some shape) ∧
      ∀ term, meaning (fun _ _ => False) shape term ↔ Accepts graph root term :=
  closed_build_total graph cyclic (reachRank graph) (cycle_ranked graph cyclic complete)
    states unique closed root present

end MicroCFTA.BinderSchedule
