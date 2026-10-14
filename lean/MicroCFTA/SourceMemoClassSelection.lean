import MicroCFTA.InternedSourceClassSelectionComplete
import MicroCFTA.SourcePredicateGateClasses

/-!
# Complete ordered class selection with both source memo tables

Every original class occurrence retains its complete unfolding and predicate
memo graphs. The original child list stays fixed. Returned constructor and
memo tables pass to every later class, including after a blocked class.
-/
namespace MicroCFTA.SourceMemoClassSelection
open Cache InternedConstructorTemplates InternedNestedConstruction
open InternedRecordCoherence InternedProbeProvenance
open SourceObservations SourceSymbolicIndex EqualityNormalize
open SourceUnconstrainedMemo (Memo Correct)
open InternedFreshOrdinaryMemoGateTrace (Ready node_ready)
open InternedFreshOrdinaryGateRank (Node fromCompleted)
open InternedSourceClassSelection (Query Trace selected select)
open SourcePredicateGateTrace (Keeps ClassReads)

local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "UMemo" => InternedFreshOrdinaryUnfoldMemo.Memo Symbol Guard
local notation "source" => SourceMemoGate.unconstrained

/-- Complete selection receipts carry both actual memo tables through every class occurrence. -/
inductive Reads [DecidableEq (EdgeKey Symbol Guard)] (values : List (Value Symbol Guard)) :
    {classes : Constraints} → {state : State Symbol Guard} → {queries : List (Query Symbol Guard)} → {final : State Symbol Guard} →
    Trace source values classes state queries final → UMemo → Memo → UMemo → Memo → Prop where
  | nil : Reads values .nil unfolding predicate unfolding predicate
  | cons (head : InternedFreshOrdinaryMemoGateTrace.ClassTrace source values paths unfolding state blocked middleUnfold middle)
      (predicateRead : ClassReads head predicate middlePredicate)
      (tail : Reads values tailTrace middleUnfold middlePredicate savedUnfold savedPredicate) :
      Reads values (.cons (InternedFreshOrdinaryMemoGateTrace.erase_class _ _ _ _ _ _ _ _ head) tailTrace)
        unfolding predicate savedUnfold savedPredicate

/-- Every complete source selection derives actual coherent calls for both memo tables. -/
theorem lift [DecidableEq (EdgeKey Symbol Guard)]
    (values : List (Value Symbol Guard)) (classes : Constraints) (state : State Symbol Guard)
    (queries : List (Query Symbol Guard)) (final : State Symbol Guard)
    (trace : Trace source values classes state queries final)
    (ready : Ready state) (available : ∀ value ∈ values, Available state value)
    (unfolding : UMemo) (unfoldCorrect : InternedFreshOrdinaryUnfoldMemo.Correct state unfolding)
    (predicate : Memo) (correct : Correct state predicate) :
    ∃ savedUnfold savedPredicate, Reads values trace unfolding predicate savedUnfold savedPredicate ∧
      Keeps state final savedUnfold savedPredicate := by
  revert correct predicate unfoldCorrect unfolding available ready
  induction trace with
  | nil =>
      intro ready available unfolding unfoldCorrect predicate correct
      exact ⟨unfolding, predicate, .nil, SourcePredicateGateTrace.pure_keeps _ _ _ ready unfoldCorrect correct⟩
  | cons head tail ih =>
      intro ready available unfolding unfoldCorrect predicate correct
      obtain ⟨middleUnfold, headUnfold, _⟩ :=
        InternedFreshOrdinaryMemoGateTrace.lift_class source _ _ _ _ _ head ready available unfolding unfoldCorrect
      obtain ⟨middlePredicate, headPredicate, headKept⟩ :=
        SourcePredicateGateTrace.lift_class _ _ _ _ _ _ _ headUnfold ready available unfoldCorrect predicate correct
      obtain ⟨savedUnfold, savedPredicate, tailReads, tailKept⟩ := ih headKept.unfolding.ready
        (fun value member => (available value member).grows _ _ headKept.unfolding.growth headKept.unfolding.history)
        middleUnfold headKept.unfolding.correct middlePredicate headKept.predicate
      exact ⟨savedUnfold, savedPredicate, .cons headUnfold headPredicate tailReads,
        SourcePredicateGateTrace.prepend_keeps headKept tailKept⟩

/-- Every ready original child list has finite stable complete selection with both actual source memos. -/
theorem complete [DecidableEq (EdgeKey Symbol Guard)] (node : Node Symbol Guard)
    (values : List (Value Symbol Guard)) (available : ∀ value ∈ values, Available node.state value) (classes : Constraints)
    (unfolding : UMemo) (unfoldCorrect : InternedFreshOrdinaryUnfoldMemo.Correct node.state unfolding)
    (predicate : Memo) (correct : Correct node.state predicate) :
    ∃ bound queries, ∃ after : Node Symbol Guard, ∃ savedUnfold savedPredicate,
      ∃ trace : Trace source values classes node.state queries after.state,
        Reads values trace unfolding predicate savedUnfold savedPredicate ∧ Keeps node.state after.state savedUnfold savedPredicate ∧
          ∀ extra, select source (bound + extra) values classes node.state = .done (some (selected queries)) after.state := by
  obtain ⟨bound, queries, after, trace, _, _, stable⟩ :=
    InternedSourceClassSelection.eventually_exact source node values available classes
  obtain ⟨savedUnfold, savedPredicate, reads, kept⟩ :=
    lift _ _ _ _ _ trace (node_ready node) available unfolding unfoldCorrect predicate correct
  exact ⟨bound, queries, after, savedUnfold, savedPredicate, trace, reads, kept, stable⟩

/-- Original source edges derive complete ordered selection with both initially empty memo tables. -/
theorem source_edges [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) :
    ∃ value state, ∃ _done : InternedFreshOrdinaryConstruction.build expression [] empty = .done value state,
      ∀ entry edges depth free, value = .node entry edges depth free → ∀ edge ∈ edges, ∀ classes,
        ∃ bound queries, ∃ after : Node Symbol Guard, ∃ savedUnfold savedPredicate,
          ∃ trace : Trace source edge.children classes state queries after.state,
            Reads edge.children trace InternedFreshOrdinaryUnfoldMemo.empty SourceUnconstrainedMemo.empty savedUnfold savedPredicate ∧
              Keeps state after.state savedUnfold savedPredicate ∧
                ∀ extra, select source (bound + extra) edge.children classes state = .done (some (selected queries)) after.state := by
  obtain ⟨value, state, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  refine ⟨value, state, done, ?_⟩
  intro entry edges depth free original edge member classes
  let node := fromCompleted expression value state done
  apply complete node edge.children ?_ classes InternedFreshOrdinaryUnfoldMemo.empty
    (InternedFreshOrdinaryUnfoldMemo.empty_correct state) SourceUnconstrainedMemo.empty (SourceUnconstrainedMemo.empty_correct state)
  intro child selected
  apply node.available.children child
  change child ∈ InternedProbeProvenance.children value
  rw [original]
  exact List.mem_flatMap.mpr ⟨edge, member, selected⟩

/-- Both memo tables compose to exactly the complete finite source selection worker. -/
theorem execution_iff [DecidableEq (EdgeKey Symbol Guard)]
    (values : List (Value Symbol Guard)) (classes : Constraints) (state : State Symbol Guard) (kept : Constraints) (final : State Symbol Guard)
    (ready : Ready state) (available : ∀ value ∈ values, Available state value)
    (unfolding : UMemo) (unfoldCorrect : InternedFreshOrdinaryUnfoldMemo.Correct state unfolding)
    (predicate : Memo) (correct : Correct state predicate) :
    (∃ fuel, select source fuel values classes state = .done (some kept) final) ↔
      ∃ queries savedUnfold savedPredicate, ∃ trace : Trace source values classes state queries final,
        kept = selected queries ∧ Reads values trace unfolding predicate savedUnfold savedPredicate ∧ Keeps state final savedUnfold savedPredicate := by
  constructor
  · rintro ⟨fuel, done⟩
    obtain ⟨queries, trace, exact⟩ := InternedSourceClassSelection.trace_of_done _ _ _ _ _ _ _ done
    obtain ⟨savedUnfold, savedPredicate, reads, kept⟩ := lift _ _ _ _ _ trace ready available unfolding unfoldCorrect predicate correct
    exact ⟨queries, savedUnfold, savedPredicate, trace, exact, reads, kept⟩
  · rintro ⟨queries, savedUnfold, savedPredicate, trace, rfl, _, _⟩
    exact InternedSourceClassSelection.trace_complete _ _ _ _ _ _ trace

/-- Saved memo choices cannot change any class receipt, selected order, or final constructor cache. -/
theorem memo_independent [DecidableEq (EdgeKey Symbol Guard)]
    (values : List (Value Symbol Guard)) (classes : Constraints) (state : State Symbol Guard)
    (firstUnfold secondUnfold firstSavedUnfold secondSavedUnfold : UMemo)
    (firstPredicate secondPredicate firstSavedPredicate secondSavedPredicate : Memo)
    (first second : List (Query Symbol Guard)) (firstState secondState : State Symbol Guard)
    (left : ∃ trace : Trace source values classes state first firstState,
      Reads values trace firstUnfold firstPredicate firstSavedUnfold firstSavedPredicate)
    (right : ∃ trace : Trace source values classes state second secondState,
      Reads values trace secondUnfold secondPredicate secondSavedUnfold secondSavedPredicate) :
    first = second ∧ selected first = selected second ∧ firstState = secondState := by
  obtain ⟨left, _⟩ := left
  obtain ⟨right, _⟩ := right
  obtain ⟨same, final⟩ := left.unique right
  exact ⟨same, congrArg selected same, final⟩

end MicroCFTA.SourceMemoClassSelection
