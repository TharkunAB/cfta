import MicroCFTA.EnumerationCPSState
import MicroCFTA.SourceUnionFindCompression

/-!
# Current union-find calls through the CPS enumeration interface

The caller reads its branch state, runs the conditional-write forest worker,
and stores that worker's returned forest. The checked correspondence keeps
execution-bound failures distinct from rejected alternatives.
-/

namespace MicroCFTA.EnumerationCPSUnionFind

open EnumerationCPSChecked EnumerationCPSState

variable {Symbol Guard : Type}

/-- The source representative caller uses the forest returned by current findRoot. -/
def representative (fuel uv : Nat) : Action Symbol Guard Nat :=
  bind get fun state =>
    match SourceUnionFindCompression.findRoot fuel state.representatives uv with
    | none => failure .representativeFuel
    | some found => bind (put {state with representatives := found.forest}) fun _ =>
        EnumerationCPSChecked.pure found.representative

/-- CPS and conditional compression preserve the complete established representative call. -/
theorem representative_exact (fuel uv : Nat) :
    Represents (representative (Symbol := Symbol) (Guard := Guard) fuel uv)
      (EnumerationState.representative fuel uv) := by
  unfold representative EnumerationState.representative
  apply bind_exact _ _ _ _ get_exact
  intro state
  rw [SourceUnionFindCompression.findRoot_eq]
  cases found : UnionFind.findRoot fuel state.representatives uv with
  | none => exact failure_exact .representativeFuel
  | some result =>
      exact bind_exact _ _ _ _ (put_exact _) (fun _ => pure_exact result.representative)

/-- The source union caller stores the forest after both conditional-write lookups. -/
def unionVariables (fuel left right : Nat) : Action Symbol Guard Unit :=
  bind get fun state =>
    match SourceUnionFindCompression.union fuel fuel state.representatives left right with
    | none => failure .representativeFuel
    | some forest => put {state with representatives := forest}

/-- The source CPS union call has the same ordered branch and final state as the proved model. -/
theorem unionVariables_exact (fuel left right : Nat) :
    Represents (unionVariables (Symbol := Symbol) (Guard := Guard) fuel left right)
      (EnumerationState.unionVariables fuel left right) := by
  unfold unionVariables EnumerationState.unionVariables
  apply bind_exact _ _ _ _ get_exact
  intro state
  rw [SourceUnionFindCompression.union_eq]
  cases found : UnionFind.union fuel fuel state.representatives left right with
  | none => exact failure_exact .representativeFuel
  | some forest => exact put_exact _

/-- The direct source representative call retains its exact result and local final state. -/
theorem representative_results (fuel uv : Nat) (state : EnumerationState.State Symbol Guard) :
    allResults (representative fuel uv) state = EnumerationState.representative fuel uv state :=
  allResults_exact _ _ (representative_exact fuel uv) state

/-- The direct source union call retains its exact result and local final state. -/
theorem unionVariables_results (fuel left right : Nat) (state : EnumerationState.State Symbol Guard) :
    allResults (unionVariables fuel left right) state = EnumerationState.unionVariables fuel left right state :=
  allResults_exact _ _ (unionVariables_exact fuel left right) state

end MicroCFTA.EnumerationCPSUnionFind
