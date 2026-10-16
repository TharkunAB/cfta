import MicroCFTA.SourceCurrentConjunctionGlobalMemos

#print axioms MicroCFTA.SourceCurrentConjunctionGlobalMemos.read_memos
#print axioms MicroCFTA.SourceCurrentConjunctionGlobalMemos.exposures_memos
#print axioms MicroCFTA.SourceCurrentConjunctionGlobalMemos.projections_memos
#print axioms MicroCFTA.SourceCurrentConjunctionGlobalMemos.classes_memos
#print axioms MicroCFTA.SourceCurrentConjunctionGlobalMemos.requirements_memos
#print axioms MicroCFTA.SourceCurrentConjunctionGlobalMemos.tuple_memos
#print axioms MicroCFTA.SourceCurrentConjunctionGlobalMemos.tuples_memos
#print axioms MicroCFTA.SourceCurrentConjunctionGlobalMemos.rows_memos
#print axioms MicroCFTA.SourceCurrentConjunctionGlobalMemos.run_memos
#print axioms MicroCFTA.SourceCurrentConjunctionGlobalMemos.decision_memos
#print axioms MicroCFTA.SourceCurrentConjunctionGlobalMemos.call_memos

#check @MicroCFTA.SourceCurrentConjunctionGlobalMemos.ReadReads
#check @MicroCFTA.SourceCurrentConjunctionGlobalMemos.ExposuresReads
#check @MicroCFTA.SourceCurrentConjunctionGlobalMemos.ProjectionsReads
#check @MicroCFTA.SourceCurrentConjunctionGlobalMemos.ClassesReads
#check @MicroCFTA.SourceCurrentConjunctionGlobalMemos.RequirementsReads
#check @MicroCFTA.SourceCurrentConjunctionGlobalMemos.TupleReads
#check @MicroCFTA.SourceCurrentConjunctionGlobalMemos.TuplesReads
#check @MicroCFTA.SourceCurrentConjunctionGlobalMemos.RowsReads
#check @MicroCFTA.SourceCurrentConjunctionGlobalMemos.RunReads
#check @MicroCFTA.SourceCurrentConjunctionGlobalMemos.DecisionReads
#check @MicroCFTA.SourceCurrentConjunctionGlobalMemos.CallReads
#check @MicroCFTA.SourceCurrentConjunctionGlobalMemos.read_memos
#check @MicroCFTA.SourceCurrentConjunctionGlobalMemos.exposures_memos
#check @MicroCFTA.SourceCurrentConjunctionGlobalMemos.projections_memos
#check @MicroCFTA.SourceCurrentConjunctionGlobalMemos.classes_memos
#check @MicroCFTA.SourceCurrentConjunctionGlobalMemos.requirements_memos
#check @MicroCFTA.SourceCurrentConjunctionGlobalMemos.tuple_memos
#check @MicroCFTA.SourceCurrentConjunctionGlobalMemos.tuples_memos
#check @MicroCFTA.SourceCurrentConjunctionGlobalMemos.rows_memos
#check @MicroCFTA.SourceCurrentConjunctionGlobalMemos.run_memos
#check @MicroCFTA.SourceCurrentConjunctionGlobalMemos.decision_memos
#check @MicroCFTA.SourceCurrentConjunctionGlobalMemos.call_memos

namespace MicroCFTA.SourceCurrentConjunctionGlobalMemosProbes
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentConjunctionGlobalMemos
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

-- Literal hits have no body reads and retain the complete global memo record.
theorem hit_exact {budget : Nat} {memo : SourceCurrentEmptinessMemo.Memo}
    {query original : Value Symbol Guard} {before : Physical} {answer : Bool} (memos : Memos)
    (found : memo query.referenceOf = some (original, answer)) :
    CallReads (SourceCurrentConjunctionMemo.Call.hit (budget := budget) (before := before) found) memos memos :=
  .hit found

-- The current open guard is a literal miss with no global reads on an arbitrary warm global table.
theorem open_miss (budget : Nat) (query : Value Symbol Guard) (before : Physical)
    (isOpen : SourceCurrentConjunctionWorklist.closed query = false)
    (memos : Memos) (valid : Valid before.heap memos) :
    CallReads (SourceCurrentConjunctionMemo.Call.miss (budget := budget)
      (memo := SourceCurrentEmptinessMemo.empty) (before := before) rfl (.open_input isOpen)) memos memos ∧
    Valid before.heap memos :=
  ⟨.miss (absent := rfl) (.open_input isOpen), valid⟩

-- A complete current call constructs its own body, fourth memo, and all three global receipts.
theorem cold_current_call (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (budget : Nat)
    (query : Value Symbol Guard) (before : Physical) (ready : Ready before)
    (available : Available before.heap query) (memos : Memos) (valid : Valid before.heap memos) :
    ∃ answer after saved final,
      ∃ actual : SourceCurrentConjunctionMemo.Call budget SourceCurrentEmptinessMemo.empty query before answer after saved,
      CallReads actual memos final ∧
      Effects before after ∧ Valid after.heap final ∧
      SourceCurrentEmptinessMemo.Correct formulas solver after.heap saved ∧
      SourceCurrentEmptinessMemo.AnswerSound formulas solver query answer ∧
      Extends memos.unfolding final.unfolding ∧ final.query = memos.query := by
  obtain ⟨answer, after, saved, actual, effects, correct, sound, _⟩ := SourceCurrentConjunctionMemo.finite
    formulas solver budget SourceCurrentEmptinessMemo.empty query before ready available
    (SourceCurrentEmptinessMemo.empty_correct formulas solver before.heap)
  obtain ⟨final, reads, coherent, retained, same⟩ := call_memos actual ready available memos valid
  exact ⟨answer, after, saved, final, actual, reads, effects, coherent, correct, sound, retained, same⟩

omit [DecidableEq Symbol] [DecidableEq (Value Symbol Guard)] in
-- A contradiction can allocate equality cache entries while adding no global read.
theorem contradiction_no_calls (tuple : List (EdgeValue Symbol Guard)) (before : Physical)
    (result : SourceEqualityConstraintAllocation.Value)
    (folded : (SourceCurrentConjunctionEquality.fold tuple before.equality).1 = .ok (some result))
    (emptyClasses : SourceEqualityInheritedPayload.classes result.payload = none) (memos : Memos) :
    TupleReads (SourceCurrentConjunctionRowsAllocation.Tuple.contradiction folded emptyClasses) memos memos :=
  .contradiction folded emptyClasses

omit [DecidableEq (Value Symbol Guard)] in
-- Actual rows retain every old unfolding entry and both exact global query tables.
theorem rows_preserve_entries {nodes : List (Value Symbol Guard)} {before after : Physical}
    {rows : List (List (List (Value Symbol Guard)))}
    (actual : SourceCurrentConjunctionRowsAllocation.Rows nodes before rows after)
    (ready : Ready before) (available : Values before.heap nodes) (closed : ClosedValues nodes)
    (memos : Memos) (valid : Valid before.heap memos) :
    ∃ saved, RowsReads actual memos saved ∧ Valid after.heap saved ∧
      saved.query.predicate = memos.query.predicate ∧ saved.query.descendants = memos.query.descendants ∧
      ∀ key entry, memos.unfolding key = some entry → saved.unfolding key = some entry := by
  obtain ⟨saved, reads, coherent, retained, same⟩ := rows_memos actual ready available closed memos valid
  exact ⟨saved, reads, coherent, congrArg SourceEndpointMemo.Memos.predicate same,
    congrArg SourceEndpointMemo.Memos.descendants same, retained⟩

end MicroCFTA.SourceCurrentConjunctionGlobalMemosProbes

#print axioms MicroCFTA.SourceCurrentConjunctionGlobalMemosProbes.hit_exact
#print axioms MicroCFTA.SourceCurrentConjunctionGlobalMemosProbes.open_miss
#print axioms MicroCFTA.SourceCurrentConjunctionGlobalMemosProbes.cold_current_call
#print axioms MicroCFTA.SourceCurrentConjunctionGlobalMemosProbes.contradiction_no_calls
#print axioms MicroCFTA.SourceCurrentConjunctionGlobalMemosProbes.rows_preserve_entries
#check @MicroCFTA.SourceCurrentConjunctionGlobalMemosProbes.hit_exact
#check @MicroCFTA.SourceCurrentConjunctionGlobalMemosProbes.open_miss
#check @MicroCFTA.SourceCurrentConjunctionGlobalMemosProbes.cold_current_call
#check @MicroCFTA.SourceCurrentConjunctionGlobalMemosProbes.contradiction_no_calls
#check @MicroCFTA.SourceCurrentConjunctionGlobalMemosProbes.rows_preserve_entries
