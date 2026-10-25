import MicroCFTA.EndpointStatefulGateGraph
import MicroCFTA.InternedFreshOrdinaryMemoGateTrace
import MicroCFTA.SourceEndpointMemoCorrect

/-!
# Three completed memo families on current gate traces

The graph records exact predicate, descendant, and unfolding memo calls.
Open ordinary endpoints skip the descendant call. Closed endpoints use its
returned pair of query memos. False siblings pass all three returned tables.
These are completed receipts. Lazy publication remains a runtime boundary.
-/
namespace MicroCFTA.EndpointMemoGateTrace
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open SourceObservations SourceSymbolicIndex EqualityNormalize
open InternedFreshOrdinaryMemoGateTrace (Ready)

local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "UMemo" => InternedFreshOrdinaryUnfoldMemo.Memo Symbol Guard
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source

/-- The current gate carries the unfolding memo and both predicate-query memos. -/
structure Memos where
  unfolding : UMemo
  query : SourceEndpointMemo.Memos

/-- All three completed tables retain exact resident inputs and source answers. -/
structure Valid [DecidableEq (EdgeKey Symbol Guard)] (heap : State Symbol Guard) (memos : Memos) : Prop where
  unfolding : InternedFreshOrdinaryUnfoldMemo.Correct heap memos.unfolding
  query : SourceEndpointMemo.Valid heap memos.query

/-- Returned tables retain constructor invariants and both constructor histories. -/
structure Keeps [DecidableEq (EdgeKey Symbol Guard)] (before after : State Symbol Guard)
    (memos : Memos) : Prop where
  ready : Ready after
  valid : Valid after memos
  growth : Grows before after
  history : Extends before.nodes.issued after.nodes.issued

/-- A query without calls retains all three tables and the complete constructor cache. -/
theorem pure_keeps [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (memos : Memos) (ready : Ready state) (valid : Valid state memos) : Keeps state state memos :=
  ⟨ready, valid, grows_refl _, extends_refl _⟩

/-- Consecutive actual queries compose their returned invariants and histories. -/
theorem prepend_keeps [DecidableEq (EdgeKey Symbol Guard)]
    {before middle after : State Symbol Guard} {firstMemos finalMemos : Memos}
    (first : Keeps before middle firstMemos) (second : Keeps middle after finalMemos) : Keeps before after finalMemos :=
  ⟨second.ready, second.valid, grows_trans first.growth second.growth, extends_trans first.history second.history⟩

mutual
/-- Exact memo receipts refine a particular completed current-policy node trace. -/
inductive NodeReads [DecidableEq (EdgeKey Symbol Guard)] :
    {path : Path} → {value : Value Symbol Guard} → {state : State Symbol Guard} →
    {answer : Bool} → {final : State Symbol Guard} →
    EndpointStatefulGateTrace.NodeTrace source reaches path value state answer final → Memos → Memos → Prop where
  | empty : NodeReads .empty memos memos
  | reference : NodeReads .reference memos memos
  | union (members : List (Value Symbol Guard)) : NodeReads (.union members) memos memos
  | finite {free : List InternedBinderProtocol.Reference} (fast : (depth == 0 && free.isEmpty) = true) :
      NodeReads (.finite fast) memos memos
  | endpoint_open {free : List InternedBinderProtocol.Reference} (slow : (depth == 0 && free.isEmpty) = false)
      (opened : free.isEmpty = false) : NodeReads (.endpoint slow) memos memos
  | endpoint_closed {free : List InternedBinderProtocol.Reference} (slow : (depth == 0 && free.isEmpty) = false)
      (closed : free.isEmpty = true)
      (actual : SourceEndpointMemo.run (.node entry edges depth free) memos.query =
        (reaches (.node entry edges depth free), savedQuery)) :
      NodeReads (.endpoint slow) memos {memos with query := savedQuery}
  | branches {free : List InternedBinderProtocol.Reference} (slow : (depth == 0 && free.isEmpty) = false)
      (trace : EdgesReads edges memos saved) : NodeReads (.branches slow edges) memos saved
  | constrained (blocked : source (.mu entry body depth ordinary) = false)
      (actual : SourceUnconstrainedMemo.run (.mu entry body depth ordinary) memos.query.predicate =
        (false, savedPredicate)) :
      NodeReads (.constrained blocked) memos {memos with query := {memos.query with predicate := savedPredicate}}
  | closed (plain : source (.mu entry body depth ordinary) = true)
      (closed : (Value.mu entry body depth ordinary).free.isEmpty = true)
      (actual : SourceUnconstrainedMemo.run (.mu entry body depth ordinary) memos.query.predicate =
        (true, savedPredicate)) :
      NodeReads (.closed plain closed) memos {memos with query := {memos.query with predicate := savedPredicate}}
  | unfold (plain : source (.mu entry body depth ordinary) = true)
      (opened : (Value.mu entry body depth ordinary).free.isEmpty = false)
      (actual : InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary) state = .done next after)
      (predicate : SourceUnconstrainedMemo.run (.mu entry body depth ordinary) memos.query.predicate =
        (true, middlePredicate))
      (unfolding : InternedFreshOrdinaryUnfoldMemo.run (.mu entry body depth ordinary) memos.unfolding state =
        .done (next, middleUnfolding) after)
      (trace : NodeReads nextTrace ⟨middleUnfolding, {memos.query with predicate := middlePredicate}⟩ saved) :
      NodeReads (.unfold plain opened actual nextTrace) memos saved

/-- A child receipt follows the actual selected physical record and all returned tables. -/
inductive ChildReads [DecidableEq (EdgeKey Symbol Guard)] :
    {values : List (Value Symbol Guard)} → {index : Nat} → {path : Path} → {state : State Symbol Guard} →
    {answer : Bool} → {final : State Symbol Guard} →
    EndpointStatefulGateTrace.ChildTrace source reaches values index path state answer final → Memos → Memos → Prop where
  | missing (absent : values[index]? = none) : ChildReads (.missing absent) memos memos
  | present (found : values[index]? = some value) (trace : NodeReads nextTrace memos saved) :
      ChildReads (.present found nextTrace) memos saved

/-- False children pass their exact three tables onward; true children omit the suffix. -/
inductive EdgesReads [DecidableEq (EdgeKey Symbol Guard)] :
    {index : Nat} → {path : Path} → {edges : List (EdgeValue Symbol Guard)} → {state : State Symbol Guard} →
    {answer : Bool} → {final : State Symbol Guard} →
    EndpointStatefulGateTrace.EdgesTrace source reaches index path edges state answer final → Memos → Memos → Prop where
  | nil : EdgesReads .nil memos memos
  | stop (head : ChildReads headTrace memos saved) : EdgesReads (.stop headTrace) memos saved
  | next (head : ChildReads headTrace memos middle) (tail : EdgesReads tailTrace middle saved) :
      EdgesReads (.next headTrace tailTrace) memos saved
end

end MicroCFTA.EndpointMemoGateTrace
