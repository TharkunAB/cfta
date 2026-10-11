import MicroCFTA.BinderCompile
import MicroCFTA.Productivity

/-!
# Component sharing in recursive graph conversion

A constructor child outside its parent's strongly connected component cannot
return to that component. Its language is independent of bindings inside the
component. The source can therefore reuse its closed shared node.
-/

namespace MicroCFTA.BinderComponents
open Language BinderLanguage BinderGraph BinderCompile Productivity

/-- One constructor edge gives a structural reachability step. -/
theorem child_reachable (graph : Automaton Nat Symbol) (root state : Nat)
    (reached : Reachable (successors graph) [root] state)
    (edge : Edge Nat Symbol) (member : edge ∈ graph state) (child : Nat) (present : child ∈ edge.children) :
    Reachable (successors graph) [root] child := by
  exact .step reached (List.mem_flatMap.mpr ⟨edge, member, present⟩)

/-- Reachability composes without a finite-universe assumption. -/
theorem reach_trans (graph : Automaton Nat Symbol) (first middle last : Nat)
    (left : Reachable (successors graph) [first] middle)
    (right : Reachable (successors graph) [middle] last) :
    Reachable (successors graph) [first] last := by
  induction right with
  | seed present => simpa using (List.mem_singleton.mp present) ▸ left
  | step _ member ih => exact .step ih member

/-- Only structurally reachable external states can affect a root run. -/
theorem run_local (graph : Automaton Nat Symbol) (active : List Nat) (left right : Env Symbol)
    (root : Nat)
    (agree : ∀ state, Reachable (successors graph) [root] state → state ∉ active → left state = right state)
    {state term} (accepted : Run graph active left state term) :
    Reachable (successors graph) [root] state → Run graph active right state term := by
  induction accepted using Run.rec
    (motive_2 := fun states terms _ =>
      (∀ state ∈ states, Reachable (successors graph) [root] state) →
        All₂ (Run graph active right) states terms) with
  | @external state term outside value =>
    intro reached
    exact .external outside (by rw [← agree state reached outside]; exact value)
  | @node state edge terms atState member runs guard ih =>
    intro reached
    exact .node edge terms atState member (ih (child_reachable graph root state reached edge member)) guard
  | nil => exact .nil
  | @cons state term states terms _ _ head tail =>
    rename_i reached
    exact .cons (head (reached state (by simp))) (tail (fun child member => reached child (by simp [member])))

/-- Equal reachable external languages give equal complete root languages. -/
theorem run_local_exact (graph : Automaton Nat Symbol) (active : List Nat) (left right : Env Symbol)
    (root : Nat)
    (agree : ∀ state, Reachable (successors graph) [root] state → state ∉ active → left state = right state) :
    Run graph active left root = Run graph active right root := by
  funext term
  apply propext
  constructor
  · intro accepted
    exact run_local graph active left right root agree accepted (.seed (by simp))
  · intro accepted
    exact run_local graph active right left root (fun state reached outside => (agree state reached outside).symm)
      accepted (.seed (by simp))

/-- Supplying original languages at the cut boundary cannot introduce a term. -/
theorem original_sound (graph : Automaton Nat Symbol) (active : List Nat) {state term}
    (accepted : Run graph active (Accepts graph) state term) : Accepts graph state term := by
  induction accepted using Run.rec
    (motive_2 := fun states terms _ => All₂ (Accepts graph) states terms) with
  | external _ original => exact original
  | node edge children _ member runs guard ih => exact .node edge children member ih guard
  | nil => exact .nil
  | cons _ _ head tail => exact .cons head tail

/-- Original graph languages can replace any set of external states. -/
theorem original_complete (graph : Automaton Nat Symbol) (active : List Nat) {state term}
    (accepted : Accepts graph state term) : Run graph active (Accepts graph) state term := by
  induction accepted using Accepts.rec
    (motive_2 := fun states terms _ => All₂ (Run graph active (Accepts graph)) states terms) with
  | @node state edge children member runs guard ih =>
    by_cases present : state ∈ active
    · exact .node edge children present member ih guard
    · exact .external present (.node edge children member runs guard)
  | nil => exact .nil
  | cons _ _ head tail => exact .cons head tail

/-- Every cut is exact when its external states use the original graph languages. -/
theorem original_exact (graph : Automaton Nat Symbol) (active : List Nat) (state : Nat) :
    Run graph active (Accepts graph) state = Accepts graph state := by
  funext term
  exact propext ⟨original_sound graph active, original_complete graph active⟩

/-- A child with no path to an altered external state can use its shared closed node. -/
theorem shared_exact (graph : Automaton Nat Symbol) (active : List Nat) (environment : Env Symbol)
    (root : Nat)
    (unchanged : ∀ state, Reachable (successors graph) [root] state → state ∉ active →
      environment state = Accepts graph state) :
    Run graph active environment root = Accepts graph root := by
  rw [run_local_exact graph active environment (Accepts graph) root unchanged]
  exact original_exact graph active root

/-- States in one strongly connected component can reach each other. -/
def SameComponent (graph : Automaton Nat Symbol) (left right : Nat) : Prop :=
  Reachable (successors graph) [left] right ∧ Reachable (successors graph) [right] left

/-- A child in a different component cannot return to any state of the parent component. -/
theorem external_child_cannot_return (graph : Automaton Nat Symbol) (parent child bound : Nat)
    (down : Reachable (successors graph) [parent] child)
    (different : ¬ SameComponent graph parent child) (inside : SameComponent graph parent bound) :
    ¬ Reachable (successors graph) [child] bound := by
  intro returned
  exact different ⟨down, reach_trans graph child bound parent returned inside.2⟩

/-- Component-local bindings do not affect a child allocated in another component. -/
theorem component_shared_exact (graph : Automaton Nat Symbol) (active : List Nat) (environment : Env Symbol)
    (parent child : Nat) (down : Reachable (successors graph) [parent] child)
    (different : ¬ SameComponent graph parent child)
    (bindingsLocal : ∀ state, ¬ SameComponent graph parent state → environment state = Accepts graph state) :
    Run graph active environment child = Accepts graph child := by
  apply shared_exact
  intro state reached _
  apply bindingsLocal
  intro same
  exact external_child_cannot_return graph parent child state down different same reached

end MicroCFTA.BinderComponents
