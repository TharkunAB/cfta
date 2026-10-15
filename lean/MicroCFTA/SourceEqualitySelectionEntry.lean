import MicroCFTA.SourceEqualityPrecheck
import MicroCFTA.SourceMemoClassSelectionReadback

/-!
# Source equality selection entry with guards and physical class order

The empty and contradiction branches run before sorting or gate selection.
The live branch uses the exact physical class order and both source memo
tables. This stage returns the selected classes before native narrowing.
-/
namespace MicroCFTA.SourceEqualitySelectionEntry
open Cache InternedConstructorTemplates InternedNestedConstruction
open InternedRecordCoherence InternedProbeProvenance SourceObservations SourceSymbolicIndex
open EqualityNormalize
open InternedFreshOrdinaryGateRank (Node fromCompleted)
open InternedSourceClassSelection (selected)
open SourcePredicateGateTrace (Keeps)
open SourceEqualityPrecheck (precheck)

local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "Input" => SourceEqualityPrecheck.Constraint
local notation "UMemo" => InternedFreshOrdinaryUnfoldMemo.Memo Symbol Guard
local notation "PMemo" => SourceUnconstrainedMemo.Memo
local notation "source" => SourceMemoGate.unconstrained

/-- The selection stage either returns immediately or supplies the complete classes for narrowing. -/
inductive Result where
  | unchanged
  | emptyChildren
  | selected (classes : Constraints)

/-- Execute only the source selection work required by the preceding physical guard result. -/
noncomputable def runChecked [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (values : List (Value Symbol Guard))
    (checked : Except String SourceEqualityPrecheck.Branch) (state : State Symbol Guard) : Outcome Symbol Guard (Except String (Option Result)) :=
  match checked with
  | .error message => .done (.error message) state
  | .ok .unchanged => .done (.ok (some .unchanged)) state
  | .ok .emptyChildren => .done (.ok (some .emptyChildren)) state
  | .ok (.classes records) =>
      (InternedSourceClassSelection.select source fuel values (records.map SourceEqualityClassOrder.Record.paths) state).bind
        fun kept after => .done (.ok (kept.map Result.selected)) after

/-- Execute the complete physical source guards before the instrumented gate filter. -/
noncomputable def run [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (values : List (Value Symbol Guard))
    (own inherited : Input) (state : State Symbol Guard) : Outcome Symbol Guard (Except String (Option Result)) :=
  runChecked fuel values (precheck own inherited) state

/-- Execute the actual array normalizer and source guards before the instrumented gate filter. -/
noncomputable def runArray [DecidableEq (EdgeKey Symbol Guard)] (work fuel : Nat) (values : List (Value Symbol Guard))
    (own inherited : Input) (state : State Symbol Guard) : Outcome Symbol Guard (Except String (Option Result)) :=
  runChecked fuel values (SourceEqualityPrecheck.precheckArray work own inherited) state

/-- Actual parent-array normalization derives the same complete entry at every sufficient work bound. -/
theorem array_eventual [DecidableEq (EdgeKey Symbol Guard)] (own inherited : Input) :
    ∃ bound, ∀ work, bound ≤ work → ∀ fuel values state,
      runArray work fuel values own inherited state = run fuel values own inherited state := by
  obtain ⟨bound, agrees⟩ := SourceEqualityPrecheck.precheckArray_eventual own inherited
  exact ⟨bound, fun work enough fuel values state => by simp only [runArray, run, agrees work enough]⟩

/-- Complete entry graphs retain both exact memo call graphs only in the live selection branch. -/
inductive Execution [DecidableEq (EdgeKey Symbol Guard)] (values : List (Value Symbol Guard)) (own inherited : Input) :
    State Symbol Guard → UMemo → PMemo → Result → State Symbol Guard → UMemo → PMemo → Prop where
  | unchanged (checked : precheck own inherited = .ok .unchanged) :
      Execution values own inherited state unfolding predicate .unchanged state unfolding predicate
  | emptyChildren (checked : precheck own inherited = .ok .emptyChildren) :
      Execution values own inherited state unfolding predicate .emptyChildren state unfolding predicate
  | select (checked : precheck own inherited = .ok (.classes records))
      (trace : InternedSourceClassSelection.Trace source values (records.map SourceEqualityClassOrder.Record.paths) state queries final)
      (reads : SourceMemoClassSelection.Reads values trace unfolding predicate savedUnfold savedPredicate) :
      Execution values own inherited state unfolding predicate (.selected (selected queries)) final savedUnfold savedPredicate

/-- Every ready entry completes with actual source prechecks, physical class order, and both coherent memo tables. -/
theorem complete [DecidableEq (EdgeKey Symbol Guard)] (node : Node Symbol Guard)
    (values : List (Value Symbol Guard)) (available : ∀ value ∈ values, Available node.state value)
    (own inherited : Input) (unfolding : UMemo) (unfoldCorrect : InternedFreshOrdinaryUnfoldMemo.Correct node.state unfolding)
    (predicate : PMemo) (predicateCorrect : SourceUnconstrainedMemo.Correct node.state predicate) :
    ∃ bound result, ∃ after : Node Symbol Guard, ∃ savedUnfold savedPredicate,
      Execution values own inherited node.state unfolding predicate result after.state savedUnfold savedPredicate ∧
        Keeps node.state after.state savedUnfold savedPredicate ∧
          ∀ extra, run (bound + extra) values own inherited node.state = .done (.ok (some result)) after.state := by
  obtain ⟨branch, checked⟩ := SourceEqualityPrecheck.precheck_safe own inherited
  cases branch with
  | unchanged =>
      exact ⟨0, .unchanged, node, unfolding, predicate, .unchanged checked,
        SourcePredicateGateTrace.pure_keeps _ _ _ (InternedFreshOrdinaryMemoGateTrace.node_ready node) unfoldCorrect predicateCorrect,
        fun extra => by simp only [run, runChecked, checked]⟩
  | emptyChildren =>
      exact ⟨0, .emptyChildren, node, unfolding, predicate, .emptyChildren checked,
        SourcePredicateGateTrace.pure_keeps _ _ _ (InternedFreshOrdinaryMemoGateTrace.node_ready node) unfoldCorrect predicateCorrect,
        fun extra => by simp only [run, runChecked, checked]⟩
  | classes records =>
      obtain ⟨bound, queries, after, savedUnfold, savedPredicate, trace, reads, kept, stable⟩ :=
        SourceMemoClassSelection.complete node values available (records.map SourceEqualityClassOrder.Record.paths)
          unfolding unfoldCorrect predicate predicateCorrect
      refine ⟨bound, .selected (selected queries), after, savedUnfold, savedPredicate, .select checked trace reads, kept, ?_⟩
      intro extra
      simp only [run, runChecked, checked, stable extra, Outcome.bind, Option.map_some]

/-- Both empty source payloads return without running a gate query, even at zero gate fuel. -/
theorem empty_entry [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (values : List (Value Symbol Guard)) (state : State Symbol Guard) :
    run fuel values (some []) (some []) state = .done (.ok (some .unchanged)) state := rfl

/-- A contradictory local payload returns before sorting or gate queries. -/
theorem local_contradiction [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat)
    (values : List (Value Symbol Guard)) (inherited : Input) (state : State Symbol Guard) :
    run fuel values none inherited state = .done (.ok (some .emptyChildren)) state := by
  simp only [run, runChecked, SourceEqualityPrecheck.local_contradiction]

/-- A contradictory inherited payload returns before sorting or gate queries. -/
theorem inherited_contradiction [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat)
    (values : List (Value Symbol Guard)) (own : Input) (state : State Symbol Guard) :
    run fuel values own none state = .done (.ok (some .emptyChildren)) state := by
  simp only [run, runChecked, SourceEqualityPrecheck.inherited_contradiction]

/-- Original source construction derives complete guarded physical selection for each original outgoing edge. -/
theorem source_edges [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) :
    ∃ value state, ∃ _done : InternedFreshOrdinaryConstruction.build expression [] empty = .done value state,
      ∀ entry edges depth free, value = .node entry edges depth free → ∀ edge ∈ edges, ∀ own inherited,
        ∃ bound result, ∃ after : Node Symbol Guard, ∃ savedUnfold savedPredicate,
          Execution edge.children own inherited state InternedFreshOrdinaryUnfoldMemo.empty SourceUnconstrainedMemo.empty
            result after.state savedUnfold savedPredicate ∧ Keeps state after.state savedUnfold savedPredicate ∧
              ∀ extra, run (bound + extra) edge.children own inherited state = .done (.ok (some result)) after.state := by
  obtain ⟨value, state, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  refine ⟨value, state, done, ?_⟩
  intro entry edges depth free original edge member own inherited
  let node := fromCompleted expression value state done
  apply complete node edge.children ?_ own inherited InternedFreshOrdinaryUnfoldMemo.empty
    (InternedFreshOrdinaryUnfoldMemo.empty_correct state) SourceUnconstrainedMemo.empty (SourceUnconstrainedMemo.empty_correct state)
  intro child selected
  apply node.available.children child
  change child ∈ InternedProbeProvenance.children value
  rw [original]
  exact List.mem_flatMap.mpr ⟨edge, member, selected⟩

/-- Original source edges derive finite actual array normalization, safe guards, physical ordering, and both memos. -/
theorem source_array_edges [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) :
    ∃ value state, ∃ _done : InternedFreshOrdinaryConstruction.build expression [] empty = .done value state,
      ∀ entry edges depth free, value = .node entry edges depth free → ∀ edge ∈ edges, ∀ own inherited,
        ∃ workBound bound result, ∃ after : Node Symbol Guard, ∃ savedUnfold savedPredicate,
          Execution edge.children own inherited state InternedFreshOrdinaryUnfoldMemo.empty SourceUnconstrainedMemo.empty
            result after.state savedUnfold savedPredicate ∧ Keeps state after.state savedUnfold savedPredicate ∧
              ∀ work, workBound ≤ work → ∀ extra,
                runArray work (bound + extra) edge.children own inherited state = .done (.ok (some result)) after.state := by
  obtain ⟨value, state, done, complete⟩ := source_edges expression
  refine ⟨value, state, done, ?_⟩
  intro entry edges depth free original edge member own inherited
  obtain ⟨bound, result, after, savedUnfold, savedPredicate, trace, kept, stable⟩ :=
    complete entry edges depth free original edge member own inherited
  obtain ⟨workBound, agrees⟩ := array_eventual own inherited
  exact ⟨workBound, bound, result, after, savedUnfold, savedPredicate, trace, kept,
    fun work enough extra => (agrees work enough _ _ _).trans (stable extra)⟩

end MicroCFTA.SourceEqualitySelectionEntry
