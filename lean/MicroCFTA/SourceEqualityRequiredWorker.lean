import MicroCFTA.SourceEqualityRequiredGraph

/-!
# Instrumented physical required-path worker

The worker keeps recursive-call bounds separate from cold-reader bounds.
Pending constructors and unresolved references remain explicit outcomes.
Actual head, edge, and node requests retain their returned caches. Bounds
instrument this logical source worker; they are not native API parameters.
-/
namespace MicroCFTA.SourceEqualityRequiredWorker
open InternedConstructorTemplates SourceEqualityNeeded

/-- The two independent proof bounds identify the operation that needs more work. -/
inductive Limit where
  | worker
  | head
  deriving DecidableEq, Repr

/-- Source failures and proof-bound exhaustion retain their exact current cache. -/
inductive Result (Symbol Guard A : Type) where
  | done (value : A) (state : State Symbol Guard)
  | pending (key : InternedBinderProtocol.NodeKey) (state : State Symbol Guard)
  | unresolved (name : InternedBinderProtocol.Reference) (state : State Symbol Guard)
  | exhausted (limit : Limit) (state : State Symbol Guard)

/-- Later work runs only after a completed value, in that value's returned cache. -/
def Result.bind (result : Result Symbol Guard A)
    (next : A → State Symbol Guard → Result Symbol Guard B) : Result Symbol Guard B :=
  match result with
  | .done value state => next value state
  | .pending key state => .pending key state
  | .unresolved name state => .unresolved name state
  | .exhausted limit state => .exhausted limit state

/-- An ordinary source constructor runs with its exact complete cache requests. -/
def work [DecidableEq (EdgeKey Symbol Guard)] (request : Work Symbol Guard A) (state : State Symbol Guard) :
    Result Symbol Guard A :=
  let actual := run request state
  .done actual.1 actual.2

/-- Expose recursive rows and construct the ordinary row node before continuing. -/
def head [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (value : Value Symbol Guard) (state : State Symbol Guard) :
    Result Symbol Guard (Value Symbol Guard) :=
  match MergedFreshOrdinaryExposure.nodeEdges fuel value state with
  | .done edges after => work (makeNode edges) after
  | .pending key after => .pending key after
  | .unresolved name after => .unresolved name after
  | .exhausted after => .exhausted .head after

/-- Visit existing children in order and apply only their stored child requirement. -/
def children (recur : Needed → Value Symbol Guard → State Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (entries : List (Int × Needed)) : Nat → List (Value Symbol Guard) → State Symbol Guard →
      Result Symbol Guard (List (Value Symbol Guard))
  | _, [], state => .done [] state
  | index, value :: rest, state =>
      match SourceEqualityNeededMap.lookup (index : Int) entries with
      | none => (children recur entries (index + 1) rest state).bind fun results after => .done (value :: results) after
      | some needed => (recur needed value state).bind fun result middle =>
          (children recur entries (index + 1) rest middle).bind fun results after => .done (result :: results) after

/-- Reject a missing required position before child work or edge reconstruction. -/
def rows [DecidableEq (EdgeKey Symbol Guard)]
    (recur : Needed → Value Symbol Guard → State Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (entries : List (Int × Needed)) : List (EdgeValue Symbol Guard) → State Symbol Guard →
      Result Symbol Guard (List (EdgeValue Symbol Guard))
  | [], state => .done [] state
  | edge :: rest, state =>
      if fits (.node entries) edge.children.length then
        (children recur entries 0 edge.children state).bind fun values middle =>
          (work (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle).bind fun result afterEdge =>
            (rows recur entries rest afterEdge).bind fun results after => .done (result :: results) after
      else rows recur entries rest state

/-- Follow source branch priority with a separate bound for repeated recursive calls. -/
def require [DecidableEq (EdgeKey Symbol Guard)] : Nat → Nat → Needed → Value Symbol Guard → State Symbol Guard →
    Result Symbol Guard (Value Symbol Guard)
  | 0, _, _, _, state => .exhausted .worker state
  | fuel + 1, readFuel, .node entries, value, state =>
      if entries.isEmpty then .done value state else
      match value with
      | .empty => .done .empty state
      | .reference name => .unresolved name state
      | .node _ edges _ _ => (rows (require fuel readFuel) entries edges state).bind fun rebuilt after => work (makeNode rebuilt) after
      | value@(.mu ..) | value@(.union ..) =>
          (head readFuel value state).bind fun exposed after => require fuel readFuel (.node entries) exposed after

/-- Empty source requirements return before inspecting an unresolved reference. -/
theorem identity [DecidableEq (EdgeKey Symbol Guard)] (fuel readFuel : Nat)
    (value : Value Symbol Guard) (state : State Symbol Guard) :
    require (fuel + 1) readFuel (.node []) value state = .done value state := rfl

/-- A nonempty source request at a bare reference reports its exact unresolved name. -/
theorem unresolved [DecidableEq (EdgeKey Symbol Guard)] (fuel readFuel : Nat)
    (entries : List (Int × Needed)) (nonempty : entries ≠ []) (name : InternedBinderProtocol.Reference)
    (state : State Symbol Guard) :
    require (fuel + 1) readFuel (.node entries) (.reference name) state = .unresolved name state := by
  simp only [require, List.isEmpty_iff, nonempty, ite_false]

end MicroCFTA.SourceEqualityRequiredWorker
