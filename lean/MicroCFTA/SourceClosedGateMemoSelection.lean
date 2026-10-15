import MicroCFTA.SourceClosedGateMemoNodes

/-!
# Ordered closed class selection with both actual source memos

Each path retains its concrete memo receipts. A true path stops its class.
Later classes use the returned predicate memo. The constructor heap and
unfolding memo stay unchanged. Physical facts and closed availability suffice.
-/
namespace MicroCFTA.SourceClosedGateMemoSelection
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceObservations SourceSymbolicIndex EqualityNormalize
open SourceUnconstrainedMemo (Memo Correct)
open InternedFreshOrdinaryStatefulGateTrace
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "UMemo" => InternedFreshOrdinaryUnfoldMemo.Memo Symbol Guard
local notation "source" => SourceMemoGate.unconstrained
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- A closed child query retains its exact lookup and both actual memo receipts. -/
theorem child {values index path before answer after} (trace : ChildTrace source values index path before answer after)
    (facts : Facts before) (available : Values before values) (closed : ClosedValues values)
    (unfolding : UMemo) (predicate : Memo) (correct : Correct before predicate) :
    ∃ saved, ∃ receipt : InternedFreshOrdinaryMemoGateTrace.ChildTrace source values index path unfolding before answer unfolding after,
      SourcePredicateGateTrace.ChildReads receipt predicate saved ∧ Correct after saved := by
  cases trace with
  | missing absent => exact ⟨predicate, .missing absent, .missing absent, correct⟩
  | present found actual =>
      have member := List.mem_of_getElem? found
      obtain ⟨saved, receipt, reads, kept⟩ := SourceClosedGateMemoNodes.node actual facts (available _ member)
        (closed _ member) unfolding predicate correct
      exact ⟨saved, .present found receipt, .present found reads, kept⟩

/-- Actual closed path queries preserve the unfolding memo and execute every reached predicate call. -/
theorem path {values position before answer after} (trace : PathTrace source values position before answer after)
    (facts : Facts before) (available : Values before values) (closed : ClosedValues values)
    (unfolding : UMemo) (predicate : Memo) (correct : Correct before predicate) :
    ∃ saved, ∃ receipt : InternedFreshOrdinaryMemoGateTrace.PathTrace source values position unfolding before answer unfolding after,
      SourcePredicateGateTrace.PathReads receipt predicate saved ∧ Correct after saved := by
  cases trace with
  | empty => exact ⟨predicate, .empty, .empty, correct⟩
  | child actual =>
      obtain ⟨saved, receipt, reads, kept⟩ := child actual facts available closed unfolding predicate correct
      exact ⟨saved, .child receipt, .child reads, kept⟩

/-- Ordered short circuit retains exactly the reached paths and returned predicate memo. -/
theorem classes {values paths before answer after} (trace : ClassTrace source values paths before answer after)
    (facts : Facts before) (available : Values before values) (closed : ClosedValues values)
    (unfolding : UMemo) (predicate : Memo) (correct : Correct before predicate) :
    ∃ saved, ∃ receipt : InternedFreshOrdinaryMemoGateTrace.ClassTrace source values paths unfolding before answer unfolding after,
      SourcePredicateGateTrace.ClassReads receipt predicate saved ∧ Correct after saved := by
  induction trace generalizing predicate with
  | nil => exact ⟨predicate, .nil, .nil, correct⟩
  | stop head =>
      obtain ⟨saved, receipt, reads, kept⟩ := path head facts available closed unfolding predicate correct
      exact ⟨saved, .stop receipt, .stop reads, kept⟩
  | next head tail ih =>
      obtain ⟨middlePredicate, first, firstReads, firstCorrect⟩ := path head facts available closed unfolding predicate correct
      have same := SourceClosedGateCache.path_state head facts available closed
      cases same
      obtain ⟨saved, rest, restReads, restCorrect⟩ := ih facts available middlePredicate firstCorrect
      exact ⟨saved, .next first rest, .next firstReads restReads, restCorrect⟩

/-- Every actual closed selection supplies both source memo tables without an unfolding cost invariant. -/
theorem selection {values classes before queries after}
    (trace : InternedSourceClassSelection.Trace source values classes before queries after)
    (facts : Facts before) (available : Values before values) (closed : ClosedValues values)
    (unfolding : UMemo) (predicate : Memo) (correct : Correct before predicate) :
    ∃ saved, SourceMemoClassSelection.Reads values trace unfolding predicate unfolding saved ∧ Correct after saved := by
  induction trace generalizing predicate with
  | nil => exact ⟨predicate, .nil, correct⟩
  | cons head tail ih =>
      obtain ⟨middlePredicate, first, firstReads, firstCorrect⟩ := SourceClosedGateMemoSelection.classes head facts available closed unfolding predicate correct
      have same := SourceClosedGateCache.class_state head facts available closed
      cases same
      obtain ⟨saved, restReads, restCorrect⟩ := ih facts available middlePredicate firstCorrect
      exact ⟨saved, .cons first firstReads restReads, restCorrect⟩

end MicroCFTA.SourceClosedGateMemoSelection
