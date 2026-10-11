import MicroCFTA.SymbolicSelection

/-!
# Residual rank bounds in the concrete symbolic decoder

The recursive count contract is explicit. It requires each successful count
to return its graph's cardinality and preserve the cache invariant. Under this
contract the source decoder keeps every residual inside the final graph's
range. A final singleton therefore has residual zero.
-/
namespace MicroCFTA.SymbolicDriver
open Language

/-- The semantic contract needed from the separate mutually recursive counter. -/
def CountSound [DecidableEq Symbol] [Ord Symbol] (graph : Graph Symbol)
    (cardinality : Nat → Nat) (invariant : Counts Symbol → Prop) : Prop :=
  ∀ fuel node initial count after, invariant initial →
    countNode graph fuel node initial = .ok (count, after) →
      count = (cardinality node : Int) ∧ invariant after

/-- Successful isolated singleton work restores its original cache snapshot. -/
theorem isolated_cache_restored (action : CountM Symbol Value) (initial after : Counts Symbol)
    (value : Value) (success : isolated action initial = .ok (value, after)) : after = initial := by
  rw [isolated_run] at success
  cases result : action initial with
  | error error => simp only [result] at success; cases success
  | ok pair =>
      rcases pair with ⟨found, ignored⟩
      simp only [result, Except.ok.injEq, Prod.mk.injEq] at success
      exact success.2.symm

def SelectionBounds [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (size : Nat → Nat)
    (invariant : Counts Symbol → Prop) (fuel : Nat) : Prop :=
  ∀ root path rank initial term final suffix after,
    invariant initial → 0 ≤ rank → rank < (size root : Int) →
    selectAt graph order fuel root path rank initial = .ok ((term, final, suffix), after) →
      invariant after ∧ suffix < (size final : Int)

def ConstructorBounds [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (size : Nat → Nat)
    (invariant : Counts Symbol → Prop) (fuel : Nat) : Prop :=
  ∀ root path rank constructors initial term final suffix after,
    constructors.Nodup → invariant initial → 0 ≤ rank →
    chooseConstructor graph order fuel root path rank constructors initial = .ok ((term, final, suffix), after) →
      invariant after ∧ suffix < (size final : Int)

def ChildrenBounds [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (size : Nat → Nat)
    (invariant : Counts Symbol → Prop) (fuel : Nat) : Prop :=
  ∀ root path rank indices initial children final suffix after,
    invariant initial → 0 ≤ rank → rank < (size root : Int) →
    selectChildren graph order fuel root path rank indices initial = .ok ((children, final, suffix), after) →
      invariant after ∧ suffix < (size final : Int)

/-- Selection preserves its residual range through the singleton shortcut or constructor blocks. -/
theorem selection_bounds_step [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (size : Nat → Nat) (invariant : Counts Symbol → Prop)
    (countsSound : CountSound graph size invariant) (fuel : Nat)
    (constructors : ConstructorBounds graph order size invariant fuel) :
    SelectionBounds graph order size invariant (fuel + 1) := by
  intro root path rank initial term final suffix after starts nonnegative bounded success
  cases counted : countNode graph fuel (graph.project path root) initial with
  | error error =>
      simp only [selectAt, Bind.bind, StateT.bind, counted, Except.bind] at success
      cases success
  | ok pair =>
      rcases pair with ⟨count, middle⟩
      have countedCorrect := countsSound fuel (graph.project path root) initial count middle starts counted
      simp only [selectAt, Bind.bind, StateT.bind, counted, Except.bind] at success
      by_cases singleton : count = 1
      · simp only [singleton, ↓reduceIte] at success
        change Except.bind (isolated (selectUnique graph order fuel (graph.project path root) []) middle)
          (fun (selected, cache) => .ok ((selected, root, rank), cache)) = .ok ((term, final, suffix), after) at success
        cases unique : isolated (selectUnique graph order fuel (graph.project path root) []) middle with
        | error error => simp only [unique, Except.bind] at success; cases success
        | ok pair =>
            rcases pair with ⟨uniqueTerm, cache⟩
            have restored := isolated_cache_restored _ middle cache uniqueTerm unique
            simp only [unique, Except.bind, Except.ok.injEq, Prod.mk.injEq] at success
            rcases success with ⟨⟨rfl, rfl, rfl⟩, rfl⟩
            exact ⟨restored ▸ countedCorrect.2, bounded⟩
      · simp only [singleton, ↓reduceIte] at success
        exact constructors root path rank (constructorsAt graph order path root) middle term final suffix after
          (constructorsAt_nodup graph order path root) countedCorrect.2 nonnegative success

/-- A selected constructor block bounds the remaining rank by its conditioned graph's count. -/
theorem constructor_bounds_step [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (size : Nat → Nat) (invariant : Counts Symbol → Prop)
    (countsSound : CountSound graph size invariant) (fuel : Nat)
    (remaining : ConstructorBounds graph order size invariant fuel)
    (childrenBound : ChildrenBounds graph order size invariant fuel) :
    ConstructorBounds graph order size invariant (fuel + 1) := by
  intro root path rank constructors initial term final suffix after distinct starts nonnegative success
  cases constructors with
  | nil => cases success
  | cons constructor rest =>
      cases counted : countNode graph fuel (graph.condition path constructor root) initial with
      | error error =>
          simp only [chooseConstructor, Bind.bind, StateT.bind, counted, Except.bind] at success
          cases success
      | ok pair =>
          rcases pair with ⟨count, middle⟩
          have countedCorrect := countsSound fuel (graph.condition path constructor root) initial count middle starts counted
          simp only [chooseConstructor, Bind.bind, StateT.bind, counted, Except.bind] at success
          by_cases skip : rank ≥ count
          · simp only [skip, ↓reduceIte] at success
            exact remaining root path (rank - count) rest middle term final suffix after
              (List.nodup_cons.mp distinct).2 countedCorrect.2 (by omega) success
          · simp only [skip, ↓reduceIte] at success
            change Except.bind
              (selectChildren graph order fuel (graph.condition path constructor root) path rank (List.range constructor.2) middle)
              (fun ((terms, last, residual), cache) => .ok ((Term.node constructor.1 terms, last, residual), cache)) =
                .ok ((term, final, suffix), after) at success
            cases selected : selectChildren graph order fuel (graph.condition path constructor root)
                path rank (List.range constructor.2) middle with
            | error error => simp only [selected, Except.bind] at success; cases success
            | ok pair =>
                rcases pair with ⟨⟨terms, last, residual⟩, cache⟩
                have decoded := childrenBound (graph.condition path constructor root) path rank (List.range constructor.2)
                  middle terms last residual cache countedCorrect.2 nonnegative (by omega) selected
                simp only [selected, Except.bind, Except.ok.injEq, Prod.mk.injEq] at success
                rcases success with ⟨⟨rfl, rfl, rfl⟩, rfl⟩
                exact decoded

/-- Every child starts with the preceding child's valid residual range and cache. -/
theorem children_bounds_step [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (size : Nat → Nat) (invariant : Counts Symbol → Prop)
    (fuel : Nat) (selection : SelectionBounds graph order size invariant fuel)
    (remaining : ChildrenBounds graph order size invariant fuel) :
    ChildrenBounds graph order size invariant (fuel + 1) := by
  intro root path rank indices initial children final suffix after starts nonnegative bounded success
  cases indices with
  | nil => cases success; exact ⟨starts, bounded⟩
  | cons index rest =>
      cases selected : selectAt graph order fuel root (path ++ [index]) rank initial with
      | error error =>
          simp only [selectChildren, Bind.bind, StateT.bind, selected, Except.bind] at success
          cases success
      | ok pair =>
          rcases pair with ⟨⟨term, restricted, residual⟩, middle⟩
          have first := selection root (path ++ [index]) rank initial term restricted residual middle starts nonnegative bounded selected
          have residualNonnegative := ((decoder_inverse_mutual graph order fuel).1 root (path ++ [index]) rank initial
            term restricted residual middle nonnegative selected).1
          cases tailSelected : selectChildren graph order fuel restricted path residual rest middle with
          | error error =>
              simp only [selectChildren, Bind.bind, StateT.bind, selected, Except.bind, tailSelected] at success
              cases success
          | ok pair =>
              rcases pair with ⟨⟨terms, last, lastRank⟩, cache⟩
              have tail := remaining restricted path residual rest middle terms last lastRank cache first.1 residualNonnegative first.2 tailSelected
              simp only [selectChildren, Bind.bind, StateT.bind, selected, Except.bind, tailSelected,
                Pure.pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at success
              rcases success with ⟨⟨rfl, rfl, rfl⟩, rfl⟩
              exact tail

/-- Source residual bounds hold for every successful bounded decoder execution. -/
theorem decoder_bounds_mutual [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (size : Nat → Nat) (invariant : Counts Symbol → Prop)
    (countsSound : CountSound graph size invariant) (fuel : Nat) :
    SelectionBounds graph order size invariant fuel ∧ ConstructorBounds graph order size invariant fuel ∧
      ChildrenBounds graph order size invariant fuel := by
  induction fuel with
  | zero =>
      refine ⟨?_, ?_, ?_⟩
      · intro root path rank initial term final suffix after starts nonnegative bounded success
        cases success
      · intro root path rank constructors initial term final suffix after distinct starts nonnegative success
        cases success
      · intro root path rank indices initial children final suffix after starts nonnegative bounded success
        cases indices with
        | nil => cases success; exact ⟨starts, bounded⟩
        | cons first rest => cases success
  | succ fuel ih =>
      exact ⟨selection_bounds_step graph order size invariant countsSound fuel ih.2.1,
        constructor_bounds_step graph order size invariant countsSound fuel ih.2.1 ih.2.2,
        children_bounds_step graph order size invariant fuel ih.1 ih.2.2⟩

/-- Once the final graph is a singleton, the concrete source decoder has consumed the complete rank. -/
theorem singleton_final_residual_zero [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (size : Nat → Nat) (invariant : Counts Symbol → Prop)
    (countsSound : CountSound graph size invariant) (fuel root : Nat) (path : List Nat) (rank : Int)
    (initial after : Counts Symbol) (term : Term Symbol) (final : Nat) (suffix : Int)
    (starts : invariant initial) (nonnegative : 0 ≤ rank) (bounded : rank < (size root : Int))
    (success : selectAt graph order fuel root path rank initial = .ok ((term, final, suffix), after))
    (singleton : size final = 1) : suffix = 0 := by
  have upper := ((decoder_bounds_mutual graph order size invariant countsSound fuel).1
    root path rank initial term final suffix after starts nonnegative bounded success).2
  have lower := ((decoder_inverse_mutual graph order fuel).1 root path rank initial term final suffix after nonnegative success).1
  rw [singleton] at upper
  omega

end MicroCFTA.SymbolicDriver
