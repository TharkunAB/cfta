import MicroCFTA.SourceTaskQueryGlobalMemos
import MicroCFTA.SourceCurrentEmptinessMemo

/-!
# Three global tables through current emptiness memo calls

Completed exploration records its actual delayed work. The initial free
check and fixed-point calculation add no global unfolding calls. A hit in
the separate emptiness memo does not execute the body. A miss executes the
current body before it saves its Boolean. These receipts keep the three
gate tables separate from the fourth Boolean memo and native request tables.
-/
namespace MicroCFTA.SourceDecisionGlobalMemos
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityNativeScoped SourceEmptinessTasks
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Value" => InternedConstructorTemplates.Value Symbol Guard
local notation "Native" => SourceRecursiveIntersectionThunks.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin

/-- Each completed closed body retains the exploration calls it actually demands. -/
inductive BodyReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] :
    {query : Value} → {before : Native width Symbol Guard} → {answer : Bool} →
    {after : Native width Symbol Guard} → SourceEmptinessDecision.Decision query before answer after → Memos → Memos → Prop where
  | empty : BodyReads .empty memos memos
  | missing (calls : SourceTaskQueryGlobalMemos.RunReads trace memos saved) :
      BodyReads (.missing nonempty trace encoded absent) memos saved
  | known (calls : SourceTaskQueryGlobalMemos.RunReads trace memos saved) :
      BodyReads (.known nonempty trace encoded present done answer) memos saved

/-- The current initial free-list guard either stops or executes the actual closed body. -/
inductive DecisionReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] :
    {query : Value} → {before : Native width Symbol Guard} → {answer : Bool} →
    {after : Native width Symbol Guard} → SourceCurrentEmptinessDecision.Decision query before answer after → Memos → Memos → Prop where
  | isOpen {query : Value} (notClosed : query.free ≠ []) : DecisionReads (.isOpen notClosed) memos memos
  | closed {query : Value} {before after : Native width Symbol Guard} {answer : Bool}
      {actual : SourceEmptinessDecision.Decision query before answer after} {memos saved : Memos}
      (closed : query.free = []) (calls : BodyReads actual memos saved) :
      DecisionReads (.closed closed actual) memos saved

/-- A fourth-memo hit skips the body; a miss retains its exact three returned gate tables. -/
inductive CallReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] :
    {memo : SourceCurrentEmptinessMemo.Memo} → {query : Value} → {before : Native width Symbol Guard} →
    {answer : Bool} → {after : Native width Symbol Guard} → {saved : SourceCurrentEmptinessMemo.Memo} →
    SourceCurrentEmptinessMemo.Call memo query before answer after saved → Memos → Memos → Prop where
  | hit {memo : SourceCurrentEmptinessMemo.Memo} {query original : Value} {answer : Bool}
      (found : memo query.referenceOf = some (original, answer)) : CallReads (.hit found) memos memos
  | miss {memo : SourceCurrentEmptinessMemo.Memo} {query : Value}
      {before after : Native width Symbol Guard} {answer : Bool}
      {actual : SourceCurrentEmptinessDecision.Decision query before answer after} {memos saved : Memos}
      (absent : memo query.referenceOf = none) (calls : DecisionReads actual memos saved) :
      CallReads (.miss absent actual) memos saved

/-- Each actual closed body derives coherent global tables and retains both query tables. -/
theorem body_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {query : Value} {before after : Native width Symbol Guard} {answer : Bool}
    (trace : SourceEmptinessDecision.Decision query before answer after)
    (ready : IdleReady top conjoin before) (costs : CostHeap before.machine.heap)
    (memos : Memos) (valid : Valid before.machine.heap memos) :
    ∃ saved, BodyReads trace memos saved ∧ Valid after.machine.heap saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  cases trace with
  | empty => exact ⟨memos, .empty, valid, extends_refl _, rfl⟩
  | missing nonempty actual encoded absent =>
      obtain ⟨saved, reads, coherent, retained, query⟩ :=
        SourceTaskQueryGlobalMemos.run_memos actual (start_ready before ready) costs memos valid
      exact ⟨saved, .missing (nonempty := nonempty) (encoded := encoded) (absent := absent) reads, coherent, retained, query⟩
  | known nonempty actual encoded present done answer =>
      obtain ⟨saved, reads, coherent, retained, query⟩ :=
        SourceTaskQueryGlobalMemos.run_memos actual (start_ready before ready) costs memos valid
      exact ⟨saved, .known (nonempty := nonempty) (encoded := encoded) (present := present) (done := done) (answer := answer) reads, coherent, retained, query⟩

/-- Every actual current decision derives its returned global tables without future validity. -/
theorem decision_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {query : Value} {before after : Native width Symbol Guard} {answer : Bool}
    (trace : SourceCurrentEmptinessDecision.Decision query before answer after)
    (ready : IdleReady top conjoin before) (costs : CostHeap before.machine.heap)
    (memos : Memos) (valid : Valid before.machine.heap memos) :
    ∃ saved, DecisionReads trace memos saved ∧ Valid after.machine.heap saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  cases trace with
  | isOpen notClosed => exact ⟨memos, .isOpen notClosed, valid, extends_refl _, rfl⟩
  | closed closed actual =>
      obtain ⟨saved, reads, coherent, retained, query⟩ := body_memos actual ready costs memos valid
      exact ⟨saved, .closed closed reads, coherent, retained, query⟩

/-- Actual fourth-memo hits and misses derive the same three coherent gate tables. -/
theorem call_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {memo saved : SourceCurrentEmptinessMemo.Memo} {query : Value}
    {before after : Native width Symbol Guard} {answer : Bool}
    (trace : SourceCurrentEmptinessMemo.Call memo query before answer after saved)
    (ready : IdleReady top conjoin before) (costs : CostHeap before.machine.heap)
    (memos : Memos) (valid : Valid before.machine.heap memos) :
    ∃ final, CallReads trace memos final ∧ Valid after.machine.heap final ∧
      Extends memos.unfolding final.unfolding ∧ final.query = memos.query := by
  cases trace with
  | hit found => exact ⟨memos, .hit found, valid, extends_refl _, rfl⟩
  | miss absent actual =>
      obtain ⟨final, reads, coherent, retained, query⟩ := decision_memos actual ready costs memos valid
      exact ⟨final, .miss absent reads, coherent, retained, query⟩

end MicroCFTA.SourceDecisionGlobalMemos
