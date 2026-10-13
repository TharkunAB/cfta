import MicroCFTA.MergedAdaptiveGroups

/-!
# A complete adaptive physical alternative-merge worker

The worker follows the source threshold, current-state comparison, retained
union guard, and actual constructor effects. Ordinary height derives enough
recursive fuel. The proof constructs every smaller-call certificate by
induction. No recursive language or termination contract is an input.
-/
namespace MicroCFTA.MergedAdaptiveMerge
open InternedConstructorTemplates InternedProbeProvenance InternedNestedProvenance
open MergedPhysicalLanguage MergedPhysicalMergeContext MergedOrdinaryHeight
open MergedAdaptiveEffects Language

noncomputable section
local instance : DecidableEq (Value Symbol Guard) := Classical.typeDecidableEq _

/-- Source merging traverses only a closed ordinary record; all other records are boundaries. -/
def worker [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (grouping : List (EdgeValue Symbol Guard) → List (List (EdgeValue Symbol Guard)))
    (outputs : List (Value Symbol Guard)) (meaning : Guard → Term Symbol → Bool)
    (unconstrained : Edge (Value Symbol Guard) Symbol → Bool) (top : Guard) :
    Nat → Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)
  | fuel, value => match value with
    | .node _ edges _ free =>
        if free = [] then
          match fuel with
          | 0 => fun _ => none
          | remaining + 1 => MergedAdaptiveGroups.root
              (worker grouping outputs meaning unconstrained top remaining) outputs meaning unconstrained top (grouping edges)
        else pure value
    | _ => pure value

/-- A source boundary returns the same complete record and exact language without effects. -/
theorem boundary_result [DecidableEq (EdgeKey Symbol Guard)]
    (state : State Symbol Guard) (outputs : List (Value Symbol Guard)) (context : Context state outputs)
    (meaning : Guard → Term Symbol → Bool) (value : Value Symbol Guard) (available : Available state value) :
    Result state state outputs meaning [value] value := by
  refine ⟨.refl state outputs context, available, ?_⟩
  intro original member term accepted
  simpa only [List.mem_singleton.mp member] using accepted

/-- Ordinary height suffices for every recursive call and the complete actual source result covers its input language. -/
theorem worker_complete [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (grouping : List (EdgeValue Symbol Guard) → List (List (EdgeValue Symbol Guard)))
    (groupsCorrect : ∀ edges, MergedPhysicalGroupRoot.Grouping edges (grouping edges))
    (outputs : List (Value Symbol Guard)) (meaning : Guard → Term Symbol → Bool)
    (unconstrained : Edge (Value Symbol Guard) Symbol → Bool)
    (clear : ∀ edge, unconstrained edge = true → ∀ term, edge.guard term = true)
    (top : Guard) (topTrue : ∀ term, meaning top term = true)
    (fuel : Nat) (value : Value Symbol Guard) (enough : height value ≤ fuel)
    (state : State Symbol Guard) (context : Context state outputs) (available : Available state value) :
    ∃ result after, worker grouping outputs meaning unconstrained top fuel value state = some (result, after) ∧
      Result state after outputs meaning [value] result := by
  induction fuel generalizing value state with
  | zero =>
      cases value with
      | empty | reference | union | mu => exact ⟨_, state, rfl, boundary_result state outputs context meaning _ available⟩
      | node entry edges depth free => simp [height] at enough
  | succ fuel ih =>
      cases value with
      | empty | reference | union | mu => exact ⟨_, state, rfl, boundary_result state outputs context meaning _ available⟩
      | node entry edges depth free =>
          by_cases closed : free = []
          · subst free
            obtain ⟨result, after, done, checked⟩ := MergedAdaptiveGroups.root_complete
              (worker grouping outputs meaning unconstrained top fuel) fuel outputs meaning unconstrained clear top topTrue
              (fun value bound state context available => ih value bound state context available)
              entry edges depth (grouping edges) (groupsCorrect edges) enough state context available
            exact ⟨result, after, by simpa only [worker, ↓reduceIte] using done, checked⟩
          · exact ⟨_, state, by simp only [worker, closed, ↓reduceIte, MergedAdaptiveEffects.pure], boundary_result state outputs context meaning _ available⟩

/-- Execute the adaptive source worker with its derived sufficient ordinary-height bound. -/
def execute [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (grouping : List (EdgeValue Symbol Guard) → List (List (EdgeValue Symbol Guard)))
    (outputs : List (Value Symbol Guard)) (meaning : Guard → Term Symbol → Bool)
    (unconstrained : Edge (Value Symbol Guard) Symbol → Bool) (top : Guard)
    (value : Value Symbol Guard) : Action Symbol Guard (Value Symbol Guard) :=
  worker grouping outputs meaning unconstrained top (height value) value

/-- Every prepared available source input has an actual completed covering result; no recursive contract remains. -/
theorem execute_complete [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (grouping : List (EdgeValue Symbol Guard) → List (List (EdgeValue Symbol Guard)))
    (groupsCorrect : ∀ edges, MergedPhysicalGroupRoot.Grouping edges (grouping edges))
    (outputs : List (Value Symbol Guard)) (meaning : Guard → Term Symbol → Bool)
    (unconstrained : Edge (Value Symbol Guard) Symbol → Bool)
    (clear : ∀ edge, unconstrained edge = true → ∀ term, edge.guard term = true)
    (top : Guard) (topTrue : ∀ term, meaning top term = true)
    (value : Value Symbol Guard) (state : State Symbol Guard)
    (context : Context state outputs) (available : Available state value) :
    ∃ result after, execute grouping outputs meaning unconstrained top value state = some (result, after) ∧
      Result state after outputs meaning [value] result :=
  worker_complete grouping groupsCorrect outputs meaning unconstrained clear top topTrue (height value) value (Nat.le_refl _) state context available

/-- The complete worker cannot exhaust its derived fuel on a prepared available source input. -/
theorem execute_ne_none [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (grouping : List (EdgeValue Symbol Guard) → List (List (EdgeValue Symbol Guard)))
    (groupsCorrect : ∀ edges, MergedPhysicalGroupRoot.Grouping edges (grouping edges))
    (outputs : List (Value Symbol Guard)) (meaning : Guard → Term Symbol → Bool)
    (unconstrained : Edge (Value Symbol Guard) Symbol → Bool)
    (clear : ∀ edge, unconstrained edge = true → ∀ term, edge.guard term = true)
    (top : Guard) (topTrue : ∀ term, meaning top term = true)
    (value : Value Symbol Guard) (state : State Symbol Guard)
    (context : Context state outputs) (available : Available state value) :
    execute grouping outputs meaning unconstrained top value state ≠ none := by
  obtain ⟨result, after, done, _⟩ := execute_complete grouping groupsCorrect outputs meaning unconstrained clear top topTrue value state context available
  simp [done]

end
end MicroCFTA.MergedAdaptiveMerge
