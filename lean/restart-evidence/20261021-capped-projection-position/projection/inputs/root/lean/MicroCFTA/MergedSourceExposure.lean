import MicroCFTA.MergedPhysicalWarmup

/-!
# Ordered physical source edge exposure

The reader follows the source's ordinary fast paths and its ordered union
closure. It records canonical numeric identities before it follows a Mu
or union. Unresolved references, pending construction, and exhausted proof
fuel remain separate outcomes.
-/
namespace MicroCFTA.MergedSourceExposure
open Cache InternedConstructorTemplates InternedNestedConstruction
open InternedBinderProtocol (Reference NodeKey)

/-- Physical edge exposure retains each source failure and the exact returned cache. -/
inductive Result (Symbol Guard : Type) where
  | done (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard)
  | unresolved (name : Reference) (state : State Symbol Guard)
  | pending (key : NodeKey) (state : State Symbol Guard)
  | exhausted (state : State Symbol Guard)

/-- Source failures and successful reads both retain their actual final cache. -/
def Result.state : Result Symbol Guard → State Symbol Guard
  | .done _ state | .unresolved _ state | .pending _ state | .exhausted state => state

/-- Process earlier ordinary edges before the remaining source worklist. -/
def Result.prepend (edges : List (EdgeValue Symbol Guard)) : Result Symbol Guard → Result Symbol Guard
  | .done rest state => .done (edges ++ rest) state
  | .unresolved name state => .unresolved name state
  | .pending key state => .pending key state
  | .exhausted state => .exhausted state

/-- Only the closure fallback applies the source edge-identity set conversion. -/
def Result.canonical : Result Symbol Guard → Result Symbol Guard
  | .done edges state => .done (canonicalEdges edges) state
  | .unresolved name state => .unresolved name state
  | .pending key state => .pending key state
  | .exhausted state => .exhausted state

/-- Follow the source's left-to-right worklist and actual cold unfolding effects. -/
def collect [DecidableEq (EdgeKey Symbol Guard)] : Nat → State Symbol Guard →
    List Nat → List (Value Symbol Guard) → Result Symbol Guard
  | _, state, _, [] => .done [] state
  | 0, state, _, _ :: _ => .exhausted state
  | fuel + 1, state, seen, value :: rest =>
      match value with
      | .empty => collect fuel state seen rest
      | .reference name => .unresolved name state
      | .node _ edges _ _ => (collect fuel state seen rest).prepend edges
      | .union entry members _ _ =>
          if entry.identity ∈ seen then collect fuel state seen rest
          else collect fuel state (entry.identity :: seen) (members ++ rest)
      | value@(.mu entry ..) =>
          if entry.identity ∈ seen then collect fuel state seen rest
          else match InternedStoredSubstitution.unfold value state with
            | .done result after => collect fuel after (entry.identity :: seen) (result :: rest)
            | .pending key after => .pending key after

/-- Expose the source's direct ordinary/Mu paths and canonicalized closure fallback. -/
def nodeEdges [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (value : Value Symbol Guard)
    (state : State Symbol Guard) : Result Symbol Guard :=
  match value with
  | .empty | .reference _ => .done [] state
  | .node _ edges _ _ => .done edges state
  | value@(.mu ..) =>
      match InternedStoredSubstitution.unfold value state with
      | .done (.node _ edges _ _) after => .done edges after
      | .done _ after => (collect fuel after [] [value]).canonical
      | .pending key after => .pending key after
  | value@(.union ..) => (collect fuel state [] [value]).canonical

/-- Completed and unresolved reads both terminate without pending construction or exhausted fuel. -/
def Finished : Result Symbol Guard → Prop
  | .done .. | .unresolved .. => True
  | .pending .. | .exhausted .. => False

/-- Prepending already-read source edges preserves termination. -/
theorem finished_prepend (edges : List (EdgeValue Symbol Guard)) (result : Result Symbol Guard) :
    Finished (result.prepend edges) ↔ Finished result := by cases result <;> rfl

/-- Canonical edge ordering preserves termination. -/
theorem finished_canonical (result : Result Symbol Guard) : Finished result.canonical ↔ Finished result := by
  cases result <;> rfl

end MicroCFTA.MergedSourceExposure
