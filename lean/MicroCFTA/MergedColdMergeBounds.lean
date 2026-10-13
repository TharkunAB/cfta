import MicroCFTA.MergedColdMerge

/-!
# Row counts of the actual cold merge worker

Successful ordered maps retain one result for each request. The literal
source threshold then limits each returned group to four rows. This count
does not bound comparison, solver, or constructor costs.
-/
namespace MicroCFTA.MergedColdMergeBounds
open InternedConstructorTemplates MergedSourceComparison MergedColdMerge

/-- A successful ordered map returns exactly one value per input request. -/
theorem map_length (call : Request → Action Symbol Guard Output) (requests : List Request)
    (state : State Symbol Guard) (values : List Output) (after : State Symbol Guard)
    (done : MergedColdMerge.map call requests state = .done values after) : values.length = requests.length := by
  induction requests generalizing state values after with
  | nil => cases done; rfl
  | cons request rest ih =>
      cases first : call request state with
      | failed => simp only [MergedColdMerge.map, MergedColdMerge.bind, first, Result.bind, reduceCtorEq] at done
      | done value middle =>
          cases tail : MergedColdMerge.map call rest middle with
          | failed => simp only [MergedColdMerge.map, MergedColdMerge.bind, first, tail, Result.bind, reduceCtorEq] at done
          | done remaining final =>
              have equal : value :: remaining = values ∧ final = after := by
                simpa only [MergedColdMerge.map, MergedColdMerge.bind, first, tail, Result.bind, MergedColdMerge.pure, Result.done.injEq] using done
              rcases equal with ⟨rfl, rfl⟩
              simpa only [List.length_cons] using congrArg Nat.succ (ih middle remaining final tail)

/-- The actual source group keeps its row count up to four and returns one row above four. -/
theorem group_length [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (recurse : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (clear : Guard → Bool) (comparisonFuel : Nat) (top : Guard) (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (rows : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (done : group recurse clear comparisonFuel top edges state = .done rows after) :
    rows.length = if edges.length ≤ 4 then edges.length else 1 := by
  by_cases small : edges.length ≤ 4
  · rw [ite_eq_left small]
    exact map_length (MergedColdMerge.small recurse) edges state rows after
      (by simpa only [group, ite_eq_left small] using done)
  · rw [ite_eq_right small]
    cases edges with
    | nil => simp at small
    | cons first rest =>
        cases built : large recurse clear comparisonFuel top first rest state with
        | failed => simp only [group, ite_eq_right small, MergedColdMerge.bind, built, Result.bind, reduceCtorEq] at done
        | done edge final =>
            have equal : [edge] = rows ∧ final = after := by
              simpa only [group, ite_eq_right small, MergedColdMerge.bind, built, Result.bind, MergedColdMerge.pure, Result.done.injEq] using done
            rw [← equal.1]
            rfl

/-- Every successful source group returns at most four edges. -/
theorem group_bound [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (recurse : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (clear : Guard → Bool) (comparisonFuel : Nat) (top : Guard) (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (rows : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (done : group recurse clear comparisonFuel top edges state = .done rows after) : rows.length ≤ 4 := by
  rw [group_length recurse clear comparisonFuel top edges state rows after done]
  split <;> omega

end MicroCFTA.MergedColdMergeBounds
