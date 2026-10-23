namespace MicroCFTA.EnumerationUntil

open Fragments EnumerationState

local instance : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

/-- The parameterized worker retains the complete eager worker action. -/
theorem enumerateOutWith_eager (graph : Graph Symbol Guard) (fuel uv : Nat) :
    enumerateOutWith graph (enumerateNode graph fuel) fuel uv = enumerateOut graph fuel uv := rfl

/-- Eager child preparation retains the old edge action at the same bound. -/
theorem enumerateEdgeWith_eager (graph : Graph Symbol Guard) (fuel : Nat)
    (scs : List Suspended) (edge : EnumerationState.Edge Symbol Guard) :
    enumerateEdgeWith (fun remaining => enumerateNode graph remaining) fuel scs edge =
      enumerateEdge graph fuel scs edge := by
  cases fuel <;> rfl

/-- A positive bounded call stops before scheduling when all candidates pass the rule. -/
theorem stop_all (graph : Graph Symbol Guard) (rule : OracleState → Nat → Bool)
    (narrow : OracleState → Nat → Nat → Nat) (expandAt : Nat → NodeExpansion Symbol Guard)
    (order : OracleState → List Nat → Option Nat) (oracle : Oracle Symbol Guard OracleState)
    (fuel : Nat) (oracleState : OracleState) (before : State Symbol Guard)
    (nonempty : (remaining graph before).isEmpty = false)
    (accepted : (remaining graph before).all (rule oracleState) = true) :
    enumerateUntil graph (some rule) narrow expandAt order oracle (fuel + 1) oracleState before =
      [.ok (some oracleState, before)] := by
  simp only [enumerateUntil]
  rw [EnumerationCorrectness.bind_single (get : EnumerateM Symbol Guard (State Symbol Guard))
    _ before before before rfl]
  simp only [nonempty, accepted, Bool.not_false, Bool.true_and, ↓reduceIte]
  rfl

end MicroCFTA.EnumerationUntil
