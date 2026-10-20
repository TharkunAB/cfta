import MicroCFTA.SourceCurrentAllocatedLocalWorker
import MicroCFTA.SourceCurrentAllocatedParentEdge

/-!
# Literal checked parent-edge reduction

Raw contradiction returns the actual sentinel before field lookup and child
work. A live field runs the local worker and checked constructor in order.
Errors, missing representation, and local failure remain distinct. Each
failure retains its actual reached checked state and both warm memos.
-/
namespace MicroCFTA.SourceCurrentAllocatedParentWorker
open Language InternedConstructorTemplates
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "contradictory" => SourceEqualityMkEdgeAllocation.contradictory
local notation "load" => SourceEqualityConstraintFieldLookup.load

/-- Parent failures preserve the phase and the complete local diagnostic. -/
inductive Fault (width : Nat) : Type 1 where
  | field (message : String)
  | missingField
  | localReduction (observation : SourceCurrentAllocatedLocalWorker.Fault width)
  | constructor (message : String)

/-- Every parent phase returns the complete checked state and both warm memos. -/
inductive Outcome (Output : Type) (width : Nat) : Type 1 where
  | done (value : Output) (checked : Checked width) (fourth : Fourth) (memo : Memo)
  | failed (fault : Fault width) (checked : Checked width) (fourth : Fourth) (memo : Memo)

def Outcome.state : Outcome Output width → Checked width
  | .done _ checked _ _ | .failed _ checked _ _ => checked

def Outcome.fourth : Outcome Output width → Fourth
  | .done _ _ fourth _ | .failed _ _ fourth _ => fourth

def Outcome.memo : Outcome Output width → Memo
  | .done _ _ _ memo | .failed _ _ _ memo => memo

/-- Only a completed phase enters its continuation at the exact returned state. -/
def Outcome.bind (first : Outcome A width)
    (next : A → Checked width → Fourth → Memo → Outcome B width) : Outcome B width :=
  match first with
  | .done value checked fourth memo => next value checked fourth memo
  | .failed fault checked fourth memo => .failed fault checked fourth memo

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
  [DecidableEq (Value Symbol Guard)] {width : Nat}

/-- A constructor error retains operations and heap reached by that same constructor. -/
noncomputable def build (symbol : Symbol) (loaded : Allocated) (children : List (Value Symbol Guard))
    (before : Checked width) (fourth : Fourth) (memo : Memo) : Outcome Edge width :=
  let actual := SourceCurrentAllocatedMkEdge.build symbol loaded children before
  match actual.1 with
  | .ok result => .done result actual.2 fourth memo
  | .error message => .failed (.constructor message) actual.2 fourth memo

/-- The local lift retains its complete diagnostic, including failed class target slots. -/
noncomputable def reduceChildren (g s r e p h m c n budget : Nat) (loaded : Allocated) (inherited : EqValue)
    (children : List (Value Symbol Guard)) (before : Checked width) (fourth : Fourth) (memo : Memo) :
    Outcome (List (Value Symbol Guard)) width :=
  match SourceCurrentAllocatedLocalWorker.reduce g s r e p h m c n budget loaded inherited children before fourth memo with
  | .done results after savedFourth saved => .done results after savedFourth saved
  | .failed fault after savedFourth saved => .failed (.localReduction fault) after savedFourth saved

/-- Raw rejection precedes loading; only a live loaded field reduces and rebuilds children. -/
noncomputable def edge (g s r e p h m c n budget : Nat) (symbol : Symbol) (original : Guard) (inherited : EqValue)
    (children : List (Value Symbol Guard)) (before : Checked width) (fourth : Fourth) (memo : Memo) : Outcome Edge width :=
  if contradictory original then
    let rejected := SourceCurrentAllocatedMkEdge.reject symbol before
    .done rejected.1 rejected.2 fourth memo
  else
    match load original before.operations.constraints with
    | .error message => .failed (.field message) before fourth memo
    | .ok none => .failed .missingField before fourth memo
    | .ok (some loaded) =>
        (reduceChildren g s r e p h m c n budget loaded inherited children before fourth memo).bind
          fun results checked savedFourth saved => build symbol loaded results checked savedFourth saved

/-- A contradictory raw guard needs no field, inherited, child, or execution-bound premise. -/
theorem edge_rejected (g s r e p h m c n budget : Nat) (symbol : Symbol) (original : Guard) (inherited : EqValue)
    (children : List (Value Symbol Guard)) (before : Checked width) (fourth : Fourth) (memo : Memo)
    (test : contradictory original = true) :
    edge g s r e p h m c n budget symbol original inherited children before fourth memo =
      .done (SourceCurrentAllocatedMkEdge.reject symbol before).1
        (SourceCurrentAllocatedMkEdge.reject symbol before).2 fourth memo := by
  simp only [edge, test, ite_true]

/-- A malformed live field retains its exact error before any local reduction. -/
theorem edge_field_error (g s r e p h m c n budget : Nat) (symbol : Symbol) (original : Guard) (inherited : EqValue)
    (children : List (Value Symbol Guard)) (before : Checked width) (fourth : Fourth) (memo : Memo)
    (message : String) (test : contradictory original = false)
    (actual : load original before.operations.constraints = .error message) :
    edge g s r e p h m c n budget symbol original inherited children before fourth memo =
      .failed (.field message) before fourth memo := by
  simp only [edge, test, Bool.false_eq_true, ite_false, actual]

/-- Missing representation remains distinct from rejection and source errors. -/
theorem edge_missing_field (g s r e p h m c n budget : Nat) (symbol : Symbol) (original : Guard) (inherited : EqValue)
    (children : List (Value Symbol Guard)) (before : Checked width) (fourth : Fourth) (memo : Memo)
    (test : contradictory original = false) (actual : load original before.operations.constraints = .ok none) :
    edge g s r e p h m c n budget symbol original inherited children before fourth memo =
      .failed .missingField before fourth memo := by
  simp only [edge, test, Bool.false_eq_true, ite_false, actual]

omit [DecidableEq Symbol] [DecidableEq (Value Symbol Guard)] in
/-- Failed checked construction retains its actual advanced operations and heap. -/
theorem build_error (symbol : Symbol) (loaded : Allocated) (children : List (Value Symbol Guard))
    (before after : Checked width) (fourth : Fourth) (memo : Memo) (message : String)
    (actual : SourceCurrentAllocatedMkEdge.build symbol loaded children before = (.error message, after)) :
    build symbol loaded children before fourth memo = .failed (.constructor message) after fourth memo := by
  simp only [build, actual]

end MicroCFTA.SourceCurrentAllocatedParentWorker
