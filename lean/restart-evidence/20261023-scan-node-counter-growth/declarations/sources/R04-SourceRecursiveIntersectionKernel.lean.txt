import MicroCFTA.SourceRecursiveIntersectionEnvironment
import MicroCFTA.SourceRecursiveIntersectionMaybeMu
import MicroCFTA.SymbolicHashJoin

/-!
# Stateful recursive source intersection caller

The caller carries the actual constructor and domain caches through each
ordered recursive request. It uses the checked physical source branch order.
Constructor pending, missing bindings, missing physical payloads, unsupported
operands, and an exhausted proof bound remain separate outcomes. The outer
native node and edge memo tables remain a separate wrapper.
-/
namespace MicroCFTA.SourceRecursiveIntersectionKernel
open Cache InternedConstructorTemplates InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionControl SourceRecursiveIntersectionDomain

/-- The source caller retains independent constructor and intersection-domain caches. -/
structure Machine (Symbol Guard : Type) where
  heap : InternedConstructorTemplates.State Symbol Guard
  domains : Cache.State DomainKey

/-- Failures preserve the source condition that prevented the next complete value. -/
inductive Failure where
  | pending (key : NodeKey)
  | missingBinder (name : Nat)
  | missingPayload (name : Nat)
  | unsupported (left right : NodeRef)
  | exhausted
  deriving DecidableEq, Repr

/-- Every source outcome retains its exact current caches. -/
inductive Result (Symbol Guard A : Type) where
  | done (value : A) (state : Machine Symbol Guard)
  | failed (failure : Failure) (state : Machine Symbol Guard)

/-- Read the actual cache after success or failure. -/
def Result.state : Result Symbol Guard A → Machine Symbol Guard
  | .done _ state | .failed _ state => state

/-- Later source calls execute only after the previous value completes. -/
def Result.bind (result : Result Symbol Guard A)
    (next : A → Machine Symbol Guard → Result Symbol Guard B) : Result Symbol Guard B :=
  match result with
  | .done value state => next value state
  | .failed failure state => .failed failure state

/-- Lift a complete constructor computation without changing the actual domain cache. -/
def work [DecidableEq (EdgeKey Symbol Guard)] (request : Work Symbol Guard A) (state : Machine Symbol Guard) :
    Result Symbol Guard A :=
  let actual := run request state.heap
  .done actual.1 {state with heap := actual.2}

/-- Lift actual Mu completion or its exact pending key without changing the domain cache. -/
def construction (outcome : InternedNestedConstruction.Outcome Symbol Guard A) (state : Machine Symbol Guard) :
    Result Symbol Guard A :=
  match outcome with
  | .done value after => .done value {state with heap := after}
  | .pending key after => .failed (.pending key) {state with heap := after}

/-- Evaluate ordered requests in the preceding request's actual returned cache. -/
def walk (call : A → Machine Symbol Guard → Result Symbol Guard B) :
    List A → Machine Symbol Guard → Result Symbol Guard (List B)
  | [], state => .done [] state
  | first :: rest, state =>
      (call first state).bind fun value after =>
        (walk call rest after).bind fun values final => .done (value :: values) final

/-- Actual Mu operands expose their stored bodies; other operands remain literal. -/
def body : Value Symbol Guard → Value Symbol Guard
  | .mu _ stored _ _ => stored
  | value => value

/-- Preserve the actual operand references when source identity cannot be forced. -/
def unsupported (left right : Value Symbol Guard) (state : Machine Symbol Guard) : Result Symbol Guard A :=
  .failed (.unsupported left.referenceOf right.referenceOf) state

/-- Allocate the extended source domain, run the actual body request, then construct its optional Mu. -/
def mu [DecidableEq (EdgeKey Symbol Guard)]
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (domain : Interned DomainKey) (left right : Value Symbol Guard) (state : Machine Symbol Guard) :
    Result Symbol Guard (Value Symbol Guard) :=
  match identity left, identity right with
  | some first, some second =>
      let entered := SourceRecursiveIntersectionEnvironment.enter state.domains domain.key left right first second
      (call entered.1 (body left) (body right) {state with domains := entered.2}).bind fun value after =>
        construction (SourceRecursiveIntersectionMaybeMu.maybeMu (pair first second) value after.heap) after
  | _, _ => unsupported left right state

/-- Resolve an original source free binding before the next recursive request. -/
def reference
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (domain : Interned DomainKey) (name : Nat) (other : Value Symbol Guard) (left : Bool) (state : Machine Symbol Guard) :
    Result Symbol Guard (Value Symbol Guard) :=
  if name ∈ names domain.key then
    match SourcePreparedSharedRows.read state.heap name with
    | some bound => if left then call domain bound other state else call domain other bound state
    | none => .failed (.missingPayload name) state
  else .failed (.missingBinder name) state

/-- Source arity mismatch constructs an empty edge before evaluating any children. -/
def edge [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (left right : EdgeValue Symbol Guard) (state : Machine Symbol Guard) : Result Symbol Guard (EdgeValue Symbol Guard) :=
  if left.children.length = right.children.length then
    (walk (fun children => call children.1 children.2) (left.children.zip right.children) state).bind fun values after =>
      work (makeEdge left.entry.key.symbol (conjoin left.entry.key.constraint right.entry.key.constraint) values) after
  else work (makeEdge left.entry.key.symbol emptyGuard [.empty]) state

/-- Source equal-symbol hash joining retains every occurrence and its bucket order. -/
def pairs [DecidableEq Symbol] (left right : List (EdgeValue Symbol Guard)) :
    List (EdgeValue Symbol Guard × EdgeValue Symbol Guard) :=
  SymbolicHashJoin.hashJoin (fun value : EdgeValue Symbol Guard => value.entry.key.symbol) Prod.mk left right

/-- Run matched source edge requests before canonical node construction. -/
def node [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (left right : List (EdgeValue Symbol Guard)) (state : Machine Symbol Guard) : Result Symbol Guard (Value Symbol Guard) :=
  (walk (fun rows => edge emptyGuard conjoin call rows.1 rows.2) (pairs left right) state).bind fun values after =>
    work (makeNode values) after

/-- Execute the actual source branch with ordered child requests and both physical cache families. -/
def onNode [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (domain : Interned DomainKey) (left right : Value Symbol Guard) (state : Machine Symbol Guard) :
    Result Symbol Guard (Value Symbol Guard) :=
  match decision domain.key left right with
  | .empty => .done .empty state
  | .reset => call IntersectionEmptyDomain.emptyDomain left right state
  | .self => .done left state
  | .swap => call domain right left state
  | .repeated key => .done (repeatedValue key) state
  | .bothMu | .leftMu | .rightMu => mu call domain left right state
  | .leftUnion => match left with
    | .union _ members _ _ =>
        (walk (fun member => call domain member right) members state).bind fun values after => work (makeUnion values) after
    | _ => unsupported left right state
  | .rightUnion => match right with
    | .union _ members _ _ =>
        (walk (fun member => call domain left member) members state).bind fun values after => work (makeUnion values) after
    | _ => unsupported left right state
  | .leftReference => match left with
    | .reference (.interned name) => reference call domain name right true state
    | _ => unsupported left right state
  | .rightReference => match right with
    | .reference (.interned name) => reference call domain name left false state
    | _ => unsupported left right state
  | .ordinary => match left, right with
    | .node _ first _ _, .node _ second _ _ => node emptyGuard conjoin (call domain) first second state
    | _, _ => unsupported left right state
  | .unsupported => unsupported left right state

/-- Bound recursive source calls explicitly without replacing exhaustion by EmptyNode. -/
def execute [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) :
    Nat → Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard)
  | 0, _, _, _, state => .failed .exhausted state
  | fuel + 1, domain, left, right, state => onNode emptyGuard conjoin (execute emptyGuard conjoin fuel) domain left right state

end MicroCFTA.SourceRecursiveIntersectionKernel
