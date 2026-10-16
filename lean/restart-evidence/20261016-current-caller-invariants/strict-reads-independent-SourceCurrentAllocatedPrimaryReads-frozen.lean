import MicroCFTA.SourceCurrentSecondaryMemos

/-!
# Current primary reads tied to their queried source records

The closed endpoint uses the same node record in its pure gate trace and
its actual descendant memo call. Older unanchored receipts remain available
under their original namespace.
-/
namespace MicroCFTA.SourceCurrentAllocatedPrimaryReads
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open SourceObservations SourceSymbolicIndex EqualityNormalize
open InternedFreshOrdinaryMemoGateTrace (Ready node_ready)
open EndpointMemoGateTrace (Memos Valid Keeps pure_keeps prepend_keeps)
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source

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
      NodeReads (EndpointStatefulGateTrace.NodeTrace.endpoint slow :
        EndpointStatefulGateTrace.NodeTrace source reaches [] (.node entry edges depth free) state
          (!free.isEmpty || reaches (.node entry edges depth free)) state)
        memos {memos with query := savedQuery}
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

/-- A primary path retains all three exact returned memo tables. -/
inductive PathReads [DecidableEq (EdgeKey Symbol Guard)] :
    {values : List (Value Symbol Guard)} → {path : Path} → {state : State Symbol Guard} →
    {answer : Bool} → {final : State Symbol Guard} →
    EndpointStatefulGateTrace.PathTrace source reaches values path state answer final → Memos → Memos → Prop where
  | empty : PathReads .empty memos memos
  | child (trace : ChildReads childTrace memos saved) : PathReads (.child childTrace) memos saved

/-- Primary false paths pass all three tables onward; true paths omit the suffix. -/
inductive ClassReads [DecidableEq (EdgeKey Symbol Guard)] :
    {values : List (Value Symbol Guard)} → {paths : Class} → {state : State Symbol Guard} →
    {answer : Bool} → {final : State Symbol Guard} →
    EndpointStatefulGateTrace.ClassTrace source reaches values paths state answer final → Memos → Memos → Prop where
  | nil : ClassReads .nil memos memos
  | stop (head : PathReads headTrace memos saved) : ClassReads (.stop headTrace) memos saved
  | next (head : PathReads headTrace memos middle) (tail : ClassReads tailTrace middle saved) :
      ClassReads (.next headTrace tailTrace) memos saved


end MicroCFTA.SourceCurrentAllocatedPrimaryReads
