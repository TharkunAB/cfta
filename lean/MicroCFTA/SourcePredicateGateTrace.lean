import MicroCFTA.SourceMemoGateSemantics

/-!
# Predicate memo receipts on complete unfolding memo graphs

These graphs retain the existing unfolding memo graph as an index. They add
the actual predicate memo call at each Mu query. Both memos pass through
false siblings in source order. A true sibling stops the scan.
-/
namespace MicroCFTA.SourcePredicateGateTrace
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open SourceObservations SourceSymbolicIndex EqualityNormalize
open SourceUnconstrainedMemo (Memo Correct run)
open InternedFreshOrdinaryMemoGateTrace (Ready)

local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "UMemo" => InternedFreshOrdinaryUnfoldMemo.Memo Symbol Guard
local notation "source" => SourceMemoGate.unconstrained

/-- A returned gate cache retains both coherent memos and every earlier constructor invariant. -/
structure Keeps [DecidableEq (EdgeKey Symbol Guard)] (before after : State Symbol Guard)
    (unfolding : UMemo) (predicate : Memo) : Prop where
  unfolding : InternedFreshOrdinaryMemoGateTrace.Keeps before after unfolding
  predicate : Correct after predicate

/-- A query without calls retains both initial memo tables. -/
theorem pure_keeps [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (unfolding : UMemo) (predicate : Memo) (ready : Ready state)
    (unfoldCorrect : InternedFreshOrdinaryUnfoldMemo.Correct state unfolding) (predicateCorrect : Correct state predicate) :
    Keeps state state unfolding predicate :=
  ⟨InternedFreshOrdinaryMemoGateTrace.pure_keeps state unfolding ready unfoldCorrect, predicateCorrect⟩

/-- Consecutive queries retain the complete returned memos and constructor histories. -/
theorem prepend_keeps [DecidableEq (EdgeKey Symbol Guard)] {before middle after : State Symbol Guard}
    {firstUnfold finalUnfold : UMemo} {firstPredicate finalPredicate : Memo}
    (first : Keeps before middle firstUnfold firstPredicate) (second : Keeps middle after finalUnfold finalPredicate) :
    Keeps before after finalUnfold finalPredicate :=
  ⟨InternedFreshOrdinaryMemoGateTrace.prepend_keeps first.unfolding second.unfolding, second.predicate⟩

mutual
/-- A node graph adds exact predicate memo receipts to its complete unfolding memo trace. -/
inductive NodeReads [DecidableEq (EdgeKey Symbol Guard)] :
    {path : Path} → {value : Value Symbol Guard} → {memo : UMemo} → {state : State Symbol Guard} →
    {answer : Bool} → {saved : UMemo} → {final : State Symbol Guard} →
    InternedFreshOrdinaryMemoGateTrace.NodeTrace source path value memo state answer saved final → Memo → Memo → Prop where
  | empty : NodeReads .empty predicate predicate
  | reference : NodeReads .reference predicate predicate
  | union (members : List (Value Symbol Guard)) : NodeReads (.union members) predicate predicate
  | finite {free : List InternedBinderProtocol.Reference} (fast : (depth == 0 && free.isEmpty) = true) : NodeReads (.finite fast) predicate predicate
  | endpoint {free : List InternedBinderProtocol.Reference} (slow : (depth == 0 && free.isEmpty) = false) : NodeReads (.endpoint slow) predicate predicate
  | branches {free : List InternedBinderProtocol.Reference} (slow : (depth == 0 && free.isEmpty) = false) (trace : EdgesReads edges predicate savedPredicate) :
      NodeReads (.branches slow edges) predicate savedPredicate
  | constrained (blocked : source (.mu entry body depth ordinary) = false)
      (actual : run (.mu entry body depth ordinary) predicate = (false, savedPredicate)) :
      NodeReads (.constrained blocked) predicate savedPredicate
  | closed (plain : source (.mu entry body depth ordinary) = true)
      (closed : (Value.mu entry body depth ordinary).free.isEmpty = true)
      (actual : run (.mu entry body depth ordinary) predicate = (true, savedPredicate)) :
      NodeReads (.closed plain closed) predicate savedPredicate
  | unfold (plain : source (.mu entry body depth ordinary) = true)
      (opened : (Value.mu entry body depth ordinary).free.isEmpty = false)
      (actual : InternedFreshOrdinaryUnfoldMemo.run (.mu entry body depth ordinary) memo state = .done (next, afterMemo) after)
      (readback : InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary) state = .done next after)
      (query : run (.mu entry body depth ordinary) predicate = (true, middlePredicate))
      (trace : NodeReads nextTrace middlePredicate savedPredicate) :
      NodeReads (.unfold plain opened actual readback nextTrace) predicate savedPredicate

/-- Child lookup retains the same selected record and the returned predicate memo. -/
inductive ChildReads [DecidableEq (EdgeKey Symbol Guard)] :
    {values : List (Value Symbol Guard)} → {index : Nat} → {path : Path} → {memo : UMemo} → {state : State Symbol Guard} →
    {answer : Bool} → {saved : UMemo} → {final : State Symbol Guard} →
    InternedFreshOrdinaryMemoGateTrace.ChildTrace source values index path memo state answer saved final → Memo → Memo → Prop where
  | missing (absent : values[index]? = none) : ChildReads (.missing absent) predicate predicate
  | present (found : values[index]? = some value) (trace : NodeReads nextTrace predicate savedPredicate) :
      ChildReads (.present found nextTrace) predicate savedPredicate

/-- Ordered edge graphs pass both memo results onward after each false child query. -/
inductive EdgesReads [DecidableEq (EdgeKey Symbol Guard)] :
    {index : Nat} → {path : Path} → {edges : List (EdgeValue Symbol Guard)} → {memo : UMemo} → {state : State Symbol Guard} →
    {answer : Bool} → {saved : UMemo} → {final : State Symbol Guard} →
    InternedFreshOrdinaryMemoGateTrace.EdgesTrace source index path edges memo state answer saved final → Memo → Memo → Prop where
  | nil : EdgesReads .nil predicate predicate
  | stop (head : ChildReads headTrace predicate savedPredicate) : EdgesReads (.stop headTrace) predicate savedPredicate
  | next (head : ChildReads headTrace predicate middlePredicate) (tail : EdgesReads tailTrace middlePredicate savedPredicate) :
      EdgesReads (.next headTrace tailTrace) predicate savedPredicate
end

end MicroCFTA.SourcePredicateGateTrace
