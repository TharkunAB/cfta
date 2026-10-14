import MicroCFTA.SourcePredicateGateLift

/-!
# Complete source gate graphs with both memo tables

Ordered paths retain both returned memo tables. Original source construction
derives finite node and class executions with exact predicate call receipts.
No completed construction, predicate law, or successful gate call is supplied.
-/
namespace MicroCFTA.SourcePredicateGateTrace
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax)
open SourceObservations SourceSymbolicIndex EqualityNormalize
open SourceUnconstrainedMemo (Memo Correct)
open InternedFreshOrdinaryMemoGateTrace (Ready node_ready)
open InternedFreshOrdinaryGateRank (Node fromCompleted)

local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "UMemo" => InternedFreshOrdinaryUnfoldMemo.Memo Symbol Guard
local notation "source" => SourceMemoGate.unconstrained

/-- A path graph retains the predicate memo returned by the selected child query. -/
inductive PathReads [DecidableEq (EdgeKey Symbol Guard)] :
    {values : List (Value Symbol Guard)} → {path : Path} → {memo : UMemo} → {state : State Symbol Guard} →
    {answer : Bool} → {saved : UMemo} → {final : State Symbol Guard} →
    InternedFreshOrdinaryMemoGateTrace.PathTrace source values path memo state answer saved final → Memo → Memo → Prop where
  | empty : PathReads .empty predicate predicate
  | child (trace : ChildReads childTrace predicate savedPredicate) : PathReads (.child childTrace) predicate savedPredicate

/-- A class graph passes both returned memo tables to each later false path. -/
inductive ClassReads [DecidableEq (EdgeKey Symbol Guard)] :
    {values : List (Value Symbol Guard)} → {paths : Class} → {memo : UMemo} → {state : State Symbol Guard} →
    {answer : Bool} → {saved : UMemo} → {final : State Symbol Guard} →
    InternedFreshOrdinaryMemoGateTrace.ClassTrace source values paths memo state answer saved final → Memo → Memo → Prop where
  | nil : ClassReads .nil predicate predicate
  | stop (head : PathReads headTrace predicate savedPredicate) : ClassReads (.stop headTrace) predicate savedPredicate
  | next (head : PathReads headTrace predicate middlePredicate) (tail : ClassReads tailTrace middlePredicate savedPredicate) :
      ClassReads (.next headTrace tailTrace) predicate savedPredicate

/-- Every complete path trace carries actual coherent predicate memo reads. -/
theorem lift_path [DecidableEq (EdgeKey Symbol Guard)]
    (values : List (Value Symbol Guard)) (path : Path) (memo : UMemo) (state : State Symbol Guard)
    (answer : Bool) (saved : UMemo) (final : State Symbol Guard)
    (trace : InternedFreshOrdinaryMemoGateTrace.PathTrace source values path memo state answer saved final)
    (ready : Ready state) (available : ∀ value ∈ values, Available state value)
    (unfoldCorrect : InternedFreshOrdinaryUnfoldMemo.Correct state memo) (predicate : Memo) (correct : Correct state predicate) :
    ∃ savedPredicate, PathReads trace predicate savedPredicate ∧ Keeps state final saved savedPredicate := by
  cases trace with
  | empty => exact ⟨predicate, .empty, pure_keeps _ _ _ ready unfoldCorrect correct⟩
  | child trace =>
      cases trace with
      | missing absent => exact ⟨predicate, .child (.missing absent), pure_keeps _ _ _ ready unfoldCorrect correct⟩
      | present found trace =>
          obtain ⟨savedPredicate, actual, kept⟩ := lift_node _ _ _ _ _ _ _ trace ready
            (available _ (List.mem_of_getElem? found)) unfoldCorrect predicate correct
          exact ⟨savedPredicate, .child (.present found actual), kept⟩

/-- Complete ordered class traces compose both coherent source memo tables. -/
theorem lift_class [DecidableEq (EdgeKey Symbol Guard)]
    (values : List (Value Symbol Guard)) (paths : Class) (memo : UMemo) (state : State Symbol Guard)
    (answer : Bool) (saved : UMemo) (final : State Symbol Guard)
    (trace : InternedFreshOrdinaryMemoGateTrace.ClassTrace source values paths memo state answer saved final)
    (ready : Ready state) (available : ∀ value ∈ values, Available state value)
    (unfoldCorrect : InternedFreshOrdinaryUnfoldMemo.Correct state memo) (predicate : Memo) (correct : Correct state predicate) :
    ∃ savedPredicate, ClassReads trace predicate savedPredicate ∧ Keeps state final saved savedPredicate := by
  revert correct predicate unfoldCorrect available ready
  induction trace with
  | nil => intro ready available unfoldCorrect predicate correct; exact ⟨predicate, .nil, pure_keeps _ _ _ ready unfoldCorrect correct⟩
  | stop head =>
      intro ready available unfoldCorrect predicate correct
      obtain ⟨savedPredicate, actual, kept⟩ := lift_path _ _ _ _ _ _ _ head ready available unfoldCorrect predicate correct
      exact ⟨savedPredicate, .stop actual, kept⟩
  | next head tail ih =>
      intro ready available unfoldCorrect predicate correct
      obtain ⟨middlePredicate, first, firstKept⟩ := lift_path _ _ _ _ _ _ _ head ready available unfoldCorrect predicate correct
      obtain ⟨savedPredicate, rest, restKept⟩ := ih firstKept.unfolding.ready
        (fun value member => (available value member).grows _ _ firstKept.unfolding.growth firstKept.unfolding.history)
        firstKept.unfolding.correct middlePredicate firstKept.predicate
      exact ⟨savedPredicate, .next first rest, prepend_keeps firstKept restKept⟩

/-- Every ready source node has finite exact execution with both actual memo call graphs. -/
theorem complete_node [DecidableEq (EdgeKey Symbol Guard)]
    (node : Node Symbol Guard) (path : Path) (memo : UMemo)
    (unfoldCorrect : InternedFreshOrdinaryUnfoldMemo.Correct node.state memo)
    (predicate : Memo) (correct : Correct node.state predicate) :
    ∃ bound answer, ∃ after : Node Symbol Guard, ∃ saved,
      ∃ trace : InternedFreshOrdinaryMemoGateTrace.NodeTrace source path node.value memo node.state answer saved after.state,
        ∃ savedPredicate, NodeReads trace predicate savedPredicate ∧ Keeps node.state after.state saved savedPredicate ∧
          ∀ extra, InternedFreshOrdinaryStatefulGate.nodeMeets source (bound + extra) path node.value node.state =
            .done (some answer) after.state := by
  obtain ⟨bound, answer, after, saved, trace, _, stable⟩ :=
    InternedFreshOrdinaryMemoGateTrace.complete_node source node path memo unfoldCorrect
  obtain ⟨savedPredicate, actual, kept⟩ := lift_node _ _ _ _ _ _ _ trace (node_ready node) node.available unfoldCorrect predicate correct
  exact ⟨bound, answer, after, saved, trace, savedPredicate, actual, kept, stable⟩

/-- Every ready complete equality class has finite exact execution with both coherent memo tables. -/
theorem complete_class [DecidableEq (EdgeKey Symbol Guard)]
    (node : Node Symbol Guard) (values : List (Value Symbol Guard)) (available : ∀ value ∈ values, Available node.state value)
    (paths : Class) (memo : UMemo) (unfoldCorrect : InternedFreshOrdinaryUnfoldMemo.Correct node.state memo)
    (predicate : Memo) (correct : Correct node.state predicate) :
    ∃ bound answer, ∃ after : Node Symbol Guard, ∃ saved,
      ∃ trace : InternedFreshOrdinaryMemoGateTrace.ClassTrace source values paths memo node.state answer saved after.state,
        ∃ savedPredicate, ClassReads trace predicate savedPredicate ∧ Keeps node.state after.state saved savedPredicate ∧
          ∀ extra, InternedFreshOrdinaryStatefulGate.classMeets source (bound + extra) values paths node.state =
            .done (some answer) after.state := by
  obtain ⟨bound, answer, after, saved, trace, _, stable⟩ :=
    InternedFreshOrdinaryMemoGateTrace.complete_class source node values available paths memo unfoldCorrect
  obtain ⟨savedPredicate, actual, kept⟩ := lift_class _ _ _ _ _ _ _ trace (node_ready node) available unfoldCorrect predicate correct
  exact ⟨bound, answer, after, saved, trace, savedPredicate, actual, kept, stable⟩

/-- Original construction derives complete node graphs with both initially empty source memo tables. -/
theorem source_nodes [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) :
    ∃ value state, ∃ _done : InternedFreshOrdinaryConstruction.build expression [] empty = .done value state,
      ∀ path, ∃ bound answer, ∃ after : Node Symbol Guard, ∃ saved,
        ∃ trace : InternedFreshOrdinaryMemoGateTrace.NodeTrace source path value InternedFreshOrdinaryUnfoldMemo.empty state answer saved after.state,
          ∃ savedPredicate, NodeReads trace SourceUnconstrainedMemo.empty savedPredicate ∧ Keeps state after.state saved savedPredicate ∧
            ∀ extra, InternedFreshOrdinaryStatefulGate.nodeMeets source (bound + extra) path value state =
              .done (some answer) after.state := by
  obtain ⟨value, state, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  exact ⟨value, state, done, fun path => complete_node (fromCompleted expression value state done) path
    InternedFreshOrdinaryUnfoldMemo.empty (InternedFreshOrdinaryUnfoldMemo.empty_correct state)
    SourceUnconstrainedMemo.empty (SourceUnconstrainedMemo.empty_correct state)⟩

/-- Original outgoing edges have complete class graphs with no supplied predicate or completed gate law. -/
theorem source_classes [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) :
    ∃ value state, ∃ _done : InternedFreshOrdinaryConstruction.build expression [] empty = .done value state,
      ∀ entry edges depth free, value = .node entry edges depth free → ∀ edge ∈ edges, ∀ paths,
        ∃ bound answer, ∃ after : Node Symbol Guard, ∃ saved,
          ∃ trace : InternedFreshOrdinaryMemoGateTrace.ClassTrace source edge.children paths InternedFreshOrdinaryUnfoldMemo.empty state answer saved after.state,
            ∃ savedPredicate, ClassReads trace SourceUnconstrainedMemo.empty savedPredicate ∧ Keeps state after.state saved savedPredicate ∧
              ∀ extra, InternedFreshOrdinaryStatefulGate.classMeets source (bound + extra) edge.children paths state =
                .done (some answer) after.state := by
  obtain ⟨value, state, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  refine ⟨value, state, done, ?_⟩
  intro entry edges depth free original edge member paths
  let node := fromCompleted expression value state done
  apply complete_class node edge.children ?_ paths InternedFreshOrdinaryUnfoldMemo.empty
    (InternedFreshOrdinaryUnfoldMemo.empty_correct state) SourceUnconstrainedMemo.empty (SourceUnconstrainedMemo.empty_correct state)
  intro child selected
  apply node.available.children child
  change child ∈ InternedProbeProvenance.children value
  rw [original]
  exact List.mem_flatMap.mpr ⟨edge, member, selected⟩

/-- Both source memos compose to exactly the original complete equality-class graph. -/
theorem class_trace_iff [DecidableEq (EdgeKey Symbol Guard)]
    (values : List (Value Symbol Guard)) (paths : Class) (state : State Symbol Guard) (answer : Bool) (final : State Symbol Guard)
    (ready : Ready state) (available : ∀ value ∈ values, Available state value)
    (memo : UMemo) (unfoldCorrect : InternedFreshOrdinaryUnfoldMemo.Correct state memo)
    (predicate : Memo) (correct : Correct state predicate) :
    InternedFreshOrdinaryStatefulGateTrace.ClassTrace source values paths state answer final ↔
      ∃ saved, ∃ trace : InternedFreshOrdinaryMemoGateTrace.ClassTrace source values paths memo state answer saved final,
        ∃ savedPredicate, ClassReads trace predicate savedPredicate ∧ Keeps state final saved savedPredicate := by
  constructor
  · intro sourceTrace
    obtain ⟨saved, trace, _⟩ := InternedFreshOrdinaryMemoGateTrace.lift_class source _ _ _ _ _ sourceTrace ready available memo unfoldCorrect
    obtain ⟨savedPredicate, actual, kept⟩ := lift_class _ _ _ _ _ _ _ trace ready available unfoldCorrect predicate correct
    exact ⟨saved, trace, savedPredicate, actual, kept⟩
  · rintro ⟨saved, trace, savedPredicate, _, _⟩
    exact InternedFreshOrdinaryMemoGateTrace.erase_class _ _ _ _ _ _ _ _ trace

/-- Different coherent memo tables retain the exact class decision and final constructor cache. -/
theorem memo_independent [DecidableEq (EdgeKey Symbol Guard)]
    (values : List (Value Symbol Guard)) (paths : Class) (state : State Symbol Guard)
    (firstMemo secondMemo firstSaved secondSaved : UMemo) (firstPredicate secondPredicate firstFinal secondFinal : Memo)
    (first second : Bool) (firstState secondState : State Symbol Guard)
    (left : ∃ trace : InternedFreshOrdinaryMemoGateTrace.ClassTrace source values paths firstMemo state first firstSaved firstState,
      ClassReads trace firstPredicate firstFinal)
    (right : ∃ trace : InternedFreshOrdinaryMemoGateTrace.ClassTrace source values paths secondMemo state second secondSaved secondState,
      ClassReads trace secondPredicate secondFinal) : first = second ∧ firstState = secondState := by
  obtain ⟨left, _⟩ := left
  obtain ⟨right, _⟩ := right
  exact InternedFreshOrdinaryMemoGateTrace.memo_independent source _ _ _ _ _ _ _ _ _ _ _ left right

end MicroCFTA.SourcePredicateGateTrace
