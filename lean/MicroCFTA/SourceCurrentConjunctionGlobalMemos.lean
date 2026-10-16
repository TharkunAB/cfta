import MicroCFTA.SourceCurrentConjunctionMemo
import MicroCFTA.SourceEqualityQueryGlobalMemos

/-!
# Three global memo tables through current conjunction emptiness

Receipts follow the actual exposure and row-major projection graphs.
Equality allocation, canonicalization, worklist guards, and the Boolean
fixed point add no global reads. A fourth-memo hit skips the body.
A miss records the current conjunction body and its exact returned heap.
Completed read receipts do not establish lazy runtime publication.
-/
namespace MicroCFTA.SourceCurrentConjunctionGlobalMemos
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentConjunctionCompletionReads (Exposures Projections Inputs jobs)
open SourceCurrentConjunctionRequirements (ClassRequirements Requirements)
open SourceCurrentConjunctionRowsAllocation (Tuple Tuples Rows Ready Effects)
open SourceCurrentConjunctionWorklist (Run PendingReady)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "EqFold" => SourceCurrentConjunctionEquality.fold

/-- A completed read records actual unfolding calls and retains both query tables. -/
def ReadReads [DecidableEq (EdgeKey Symbol Guard)]
    {value : Value Symbol Guard} {before after : State Symbol Guard} {edges : List (EdgeValue Symbol Guard)}
    (actual : SourceEqualityProjectionRead.Read value before edges after) (memos saved : Memos) : Prop :=
  SourceEqualityProjectionMemos.ReadReads actual memos.unfolding saved.unfolding ∧ saved.query = memos.query

/-- Operand occurrences pass returned tables through their actual exposure order. -/
inductive ExposuresReads [DecidableEq (EdgeKey Symbol Guard)] :
    {values : List (Value Symbol Guard)} → {before after : State Symbol Guard} →
    {edges : List (List (EdgeValue Symbol Guard))} → Exposures values before edges after → Memos → Memos → Prop where
  | nil : ExposuresReads .nil memos memos
  | cons (first : ReadReads firstTrace memos middle) (rest : ExposuresReads restTrace middle saved) :
      ExposuresReads (.cons firstTrace restTrace) memos saved

/-- Projection jobs retain their literal row-major order and exact heap snapshots. -/
inductive ProjectionsReads [DecidableEq (EdgeKey Symbol Guard)] :
    {jobs : List (SourceCurrentConjunctionCompletionReads.Job Symbol Guard)} →
    {before after : State Symbol Guard} → {values : List (Value Symbol Guard)} →
    Projections jobs before values after → Memos → Memos → Prop where
  | nil : ProjectionsReads .nil memos memos
  | cons (first : SourceEqualityQueryGlobalMemos.ProjectionReads firstTrace memos middle)
      (rest : ProjectionsReads restTrace middle saved) : ProjectionsReads (.cons firstTrace restTrace) memos saved

/-- Class requirements pass each returned table to the next actual class. -/
inductive ClassesReads [DecidableEq (EdgeKey Symbol Guard)] :
    {forests : List (List (Value Symbol Guard))} → {classes : EqualityNormalize.Constraints} →
    {before after : State Symbol Guard} → {requirements : List (List (Value Symbol Guard))} →
    ClassRequirements forests classes before requirements after → Memos → Memos → Prop where
  | nil : ClassesReads .nil memos memos
  | cons (first : ProjectionsReads firstTrace memos middle) (rest : ClassesReads restTrace middle saved) :
      ClassesReads (.cons firstTrace restTrace) memos saved

/-- Column canonicalization adds no global calls before actual class requirements. -/
inductive RequirementsReads [DecidableEq (EdgeKey Symbol Guard)] :
    {tuple : List (EdgeValue Symbol Guard)} → {classes : EqualityNormalize.Constraints} →
    {before after : State Symbol Guard} → {requirements : List (List (Value Symbol Guard))} →
    Requirements tuple classes before requirements after → Memos → Memos → Prop where
  | run (calls : ClassesReads actual memos saved) : RequirementsReads (.run sameArity actual) memos saved

/-- Equality allocation itself leaves the three global tables unchanged. -/
inductive TupleReads [DecidableEq (EdgeKey Symbol Guard)] :
    {tuple : List (EdgeValue Symbol Guard)} → {before after : Physical} →
    {row : Option (List (List (Value Symbol Guard)))} → Tuple tuple before row after → Memos → Memos → Prop where
  | contradiction {tuple : List (EdgeValue Symbol Guard)} {before : Physical}
      {result : SourceEqualityConstraintAllocation.Value} {memos : Memos}
      (folded : (EqFold tuple before.equality).1 = .ok (some result))
      (emptyClasses : SourceEqualityInheritedPayload.classes result.payload = none) :
      TupleReads (.contradiction folded emptyClasses) memos memos
  | live (calls : RequirementsReads actual memos saved) : TupleReads (.live folded classes actual) memos saved

/-- Tuple skips and retained rows pass the same actual returned tables in source order. -/
inductive TuplesReads [DecidableEq (EdgeKey Symbol Guard)] :
    {tuples : List (List (EdgeValue Symbol Guard))} → {before after : Physical} →
    {rows : List (List (List (Value Symbol Guard)))} → Tuples tuples before rows after → Memos → Memos → Prop where
  | nil : TuplesReads .nil memos memos
  | skip (first : TupleReads firstTrace memos middle) (rest : TuplesReads restTrace middle saved) :
      TuplesReads (.skip firstTrace restTrace) memos saved
  | keep (first : TupleReads firstTrace memos middle) (rest : TuplesReads restTrace middle saved) :
      TuplesReads (.keep firstTrace restTrace) memos saved

/-- Every admitted row records exposures before its allocated tuple requirements. -/
inductive RowsReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] :
    {nodes : List (Value Symbol Guard)} → {before after : Physical} →
    {rows : List (List (List (Value Symbol Guard)))} → Rows nodes before rows after → Memos → Memos → Prop where
  | run (exposed : ExposuresReads reads memos middle) (allocated : TuplesReads tuples middle saved) :
      RowsReads (.run reads tuples) memos saved

/-- Worklist receipts follow only actual admissions and visited pending suffixes. -/
inductive RunReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] :
    {budget : Nat} → {table final : List (SourceCurrentConjunctionEmptinessTable.Entry (Value Symbol Guard))} →
    {pending : List (List (Value Symbol Guard))} → {before after : Physical} →
    Run budget table pending before final after → Memos → Memos → Prop where
  | done : RunReads .done memos memos
  | empty (rest : RunReads actual memos saved) : RunReads (.empty impossible actual) memos saved
  | skip (rest : RunReads actual memos saved) : RunReads (.skip nonempty skipped actual) memos saved
  | admit (rows : RowsReads rowsTrace memos middle) (rest : RunReads restTrace middle saved) :
      RunReads (.admit nonempty fresh rowsTrace restTrace) memos saved

/-- The free-list guard and final Boolean grow calculation add no global calls. -/
inductive DecisionReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] :
    {budget : Nat} → {start : Value Symbol Guard} → {before after : Physical} → {answer : Bool} →
    SourceCurrentConjunctionDecision.Decision budget start before answer after → Memos → Memos → Prop where
  | open_input (isOpen : SourceCurrentConjunctionWorklist.closed start = false) :
      DecisionReads (.open_input isOpen) memos memos
  | closed (calls : RunReads actual memos saved) : DecisionReads (.closed isClosed actual grown) memos saved

/-- Hits skip the body. Misses retain the exact current conjunction decision reads. -/
inductive CallReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] :
    {budget : Nat} → {memo saved : SourceCurrentEmptinessMemo.Memo} → {query : Value Symbol Guard} →
    {before after : Physical} → {answer : Bool} →
    SourceCurrentConjunctionMemo.Call budget memo query before answer after saved → Memos → Memos → Prop where
  | hit {budget : Nat} {memo : SourceCurrentEmptinessMemo.Memo} {query original : Value Symbol Guard}
      {answer : Bool} {before : Physical} {memos : Memos}
      (found : memo query.referenceOf = some (original, answer)) :
      CallReads (SourceCurrentConjunctionMemo.Call.hit (budget := budget) (before := before) found) memos memos
  | miss (calls : DecisionReads actual memos saved) : CallReads (.miss absent actual) memos saved

/-- Actual bounded exposure derives the three coherent tables at its exact returned heap. -/
theorem read_memos [DecidableEq (EdgeKey Symbol Guard)]
    {value : Value Symbol Guard} {before after : State Symbol Guard} {edges : List (EdgeValue Symbol Guard)}
    (actual : SourceEqualityProjectionRead.Read value before edges after) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Available before value) (memos : Memos) (valid : Valid before memos) :
    ∃ saved, ReadReads actual memos saved ∧ Valid after saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  cases actual with
  | done fuel completed =>
      obtain ⟨saved, reads, coherent, retained⟩ :=
        SourceEqualityQueryGlobalMemos.exposure_memos fuel value before semantic costs available memos valid
      exact ⟨saved, ⟨.done (actual := completed) reads.1, reads.2⟩,
        by simpa only [completed, MergedSourceExposure.Result.state] using coherent, retained, reads.2⟩

/-- Actual sequential exposure derives every next heap and memo premise. -/
theorem exposures_memos [DecidableEq (EdgeKey Symbol Guard)]
    {values : List (Value Symbol Guard)} {before after : State Symbol Guard}
    {edges : List (List (EdgeValue Symbol Guard))} (actual : Exposures values before edges after)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before values)
    (memos : Memos) (valid : Valid before memos) :
    ∃ saved, ExposuresReads actual memos saved ∧ Valid after saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  induction actual generalizing memos with
  | nil => exact ⟨memos, .nil, valid, extends_refl _, rfl⟩
  | @cons value before edges middle values more after first rest ih =>
      obtain ⟨middleMemo, reads, coherent, retained, same⟩ := read_memos first semantic costs
        (available _ List.mem_cons_self) memos valid
      have own := SourceEqualityProjectionCosts.read_effects first semantic costs (available _ List.mem_cons_self)
      obtain ⟨saved, suffix, finalValid, finalRetained, finalSame⟩ := ih own.2.1 own.2.2.1
        (fun value member => own.1.available value (available value (List.mem_cons_of_mem _ member))) middleMemo coherent
      exact ⟨saved, .cons reads suffix, finalValid, extends_trans retained finalRetained, finalSame.trans same⟩

/-- Literal row-major projection jobs retain earlier unfoldings and both original query tables. -/
theorem projections_memos [DecidableEq (EdgeKey Symbol Guard)]
    {work : List (SourceCurrentConjunctionCompletionReads.Job Symbol Guard)} {before after : State Symbol Guard}
    {values : List (Value Symbol Guard)} (actual : Projections work before values after)
    (semantic : SemanticReady before) (costs : CostHeap before) (inputs : Inputs before work)
    (memos : Memos) (valid : Valid before memos) :
    ∃ saved, ProjectionsReads actual memos saved ∧ Valid after saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  induction actual generalizing memos with
  | nil => exact ⟨memos, .nil, valid, extends_refl _, rfl⟩
  | @cons forest path before value middle remaining values after first rest ih =>
      have ownInputs := inputs _ List.mem_cons_self
      obtain ⟨middleMemo, reads, coherent, retained⟩ := SourceEqualityQueryGlobalMemos.forest_memos first
        semantic costs ownInputs.1 memos valid
      have own := SourceEqualityProjectionCosts.forest_effects first semantic costs ownInputs.1
      obtain ⟨saved, suffix, finalValid, finalRetained, finalSame⟩ := ih own.2.1 own.2.2.1
        (SourceCurrentConjunctionCompletionReads.Inputs.keeps
          (fun job member => inputs job (List.mem_cons_of_mem _ member)) own.1) middleMemo coherent
      exact ⟨saved, .cons reads suffix, finalValid, extends_trans retained finalRetained, finalSame.trans reads.2⟩

/-- Actual class requirements derive each following projection's physical inputs. -/
theorem classes_memos [DecidableEq (EdgeKey Symbol Guard)]
    {forests : List (List (Value Symbol Guard))} {classes : EqualityNormalize.Constraints}
    {before after : State Symbol Guard} {requirements : List (List (Value Symbol Guard))}
    (actual : ClassRequirements forests classes before requirements after) (semantic : SemanticReady before)
    (costs : CostHeap before) (inputs : SourceCurrentConjunctionRequirements.RowsReady before forests)
    (memos : Memos) (valid : Valid before memos) :
    ∃ saved, ClassesReads actual memos saved ∧ Valid after saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  induction actual generalizing memos with
  | nil => exact ⟨memos, .nil, valid, extends_refl _, rfl⟩
  | @cons paths before projected middle classes requirements after first rest ih =>
      have jobsReady := SourceCurrentConjunctionCompletionReads.jobs_inputs before forests paths
        (fun forest member => (inputs forest member).1) (fun forest member => (inputs forest member).2)
      obtain ⟨middleMemo, reads, coherent, retained, same⟩ := projections_memos first semantic costs jobsReady memos valid
      have own := first.verified (fun _ => True) semantic costs (fun _ _ _ => trivial) jobsReady
      obtain ⟨saved, suffix, finalValid, finalRetained, finalSame⟩ := ih own.1.semantic own.1.costs
        (fun forest member => ⟨fun value included => own.1.keeps.available value ((inputs forest member).1 value included),
          (inputs forest member).2⟩) middleMemo coherent
      exact ⟨saved, .cons reads suffix, finalValid, extends_trans retained finalRetained, finalSame.trans same⟩

/-- Child columns and equality allocation add no calls before the actual class projection list. -/
theorem requirements_memos [DecidableEq (EdgeKey Symbol Guard)]
    {tuple : List (EdgeValue Symbol Guard)} {classes : EqualityNormalize.Constraints}
    {before after : State Symbol Guard} {requirements : List (List (Value Symbol Guard))}
    (actual : Requirements tuple classes before requirements after) (semantic : SemanticReady before)
    (costs : CostHeap before) (resident : Edges before tuple) (closed : ClosedEdges tuple)
    (memos : Memos) (valid : Valid before memos) :
    ∃ saved, RequirementsReads actual memos saved ∧ Valid after saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  cases actual with
  | run sameArity actual =>
      obtain ⟨saved, reads, coherent, retained, same⟩ := classes_memos actual semantic costs
        (SourceCurrentConjunctionRequirements.tuple_inputs tuple before semantic resident closed) memos valid
      exact ⟨saved, .run (sameArity := sameArity) reads, coherent, retained, same⟩

/-- An actual tuple's equality fold changes no global table before its live projections. -/
theorem tuple_memos [DecidableEq (EdgeKey Symbol Guard)]
    {tuple : List (EdgeValue Symbol Guard)} {before after : Physical}
    {row : Option (List (List (Value Symbol Guard)))} (actual : Tuple tuple before row after)
    (ready : Ready before) (resident : Edges before.heap tuple) (closed : ClosedEdges tuple)
    (memos : Memos) (valid : Valid before.heap memos) :
    ∃ saved, TupleReads actual memos saved ∧ Valid after.heap saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  cases actual with
  | contradiction folded emptyClasses =>
      exact ⟨memos, .contradiction folded emptyClasses, valid, extends_refl _, rfl⟩
  | live folded classes requirements =>
      obtain ⟨saved, reads, coherent, retained, same⟩ := requirements_memos requirements ready.semantic ready.costs
        resident closed memos valid
      exact ⟨saved, .live (folded := folded) (classes := classes) reads, coherent, retained, same⟩

/-- Actual tuple prefixes derive the ready states used by every following global read. -/
theorem tuples_memos [DecidableEq (EdgeKey Symbol Guard)]
    {tuples : List (List (EdgeValue Symbol Guard))} {before after : Physical}
    {rows : List (List (List (Value Symbol Guard)))} (actual : Tuples tuples before rows after)
    (ready : Ready before) (resident : ∀ tuple ∈ tuples, Edges before.heap tuple)
    (closed : ∀ tuple ∈ tuples, ClosedEdges tuple) (memos : Memos) (valid : Valid before.heap memos) :
    ∃ saved, TuplesReads actual memos saved ∧ Valid after.heap saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  induction actual generalizing memos with
  | nil => exact ⟨memos, .nil, valid, extends_refl _, rfl⟩
  | @skip tuple before middle tuples rows after first rest ih =>
      have own := first.verified ready (resident tuple List.mem_cons_self) (closed tuple List.mem_cons_self)
      obtain ⟨middleMemo, reads, coherent, retained, same⟩ := tuple_memos first ready
        (resident tuple List.mem_cons_self) (closed tuple List.mem_cons_self) memos valid
      obtain ⟨saved, suffix, finalValid, finalRetained, finalSame⟩ := ih own.1.ready
        (fun chosen member edge included => InternedEdgeResidency.edge_grows before.heap middle.heap own.1.keeps.growth
          edge (resident chosen (List.mem_cons_of_mem _ member) edge included))
        (fun chosen member => closed chosen (List.mem_cons_of_mem _ member)) middleMemo coherent
      exact ⟨saved, .skip reads suffix, finalValid, extends_trans retained finalRetained, finalSame.trans same⟩
  | @keep tuple before row middle tuples rows after first rest ih =>
      have own := first.verified ready (resident tuple List.mem_cons_self) (closed tuple List.mem_cons_self)
      obtain ⟨middleMemo, reads, coherent, retained, same⟩ := tuple_memos first ready
        (resident tuple List.mem_cons_self) (closed tuple List.mem_cons_self) memos valid
      obtain ⟨saved, suffix, finalValid, finalRetained, finalSame⟩ := ih own.1.ready
        (fun chosen member edge included => InternedEdgeResidency.edge_grows before.heap middle.heap own.1.keeps.growth
          edge (resident chosen (List.mem_cons_of_mem _ member) edge included))
        (fun chosen member => closed chosen (List.mem_cons_of_mem _ member)) middleMemo coherent
      exact ⟨saved, .keep reads suffix, finalValid, extends_trans retained finalRetained, finalSame.trans same⟩

/-- One actual admitted conjunction derives all three final tables from its initial physical facts. -/
theorem rows_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {nodes : List (Value Symbol Guard)} {before after : Physical}
    {rows : List (List (List (Value Symbol Guard)))} (actual : Rows nodes before rows after)
    (ready : Ready before) (available : Values before.heap nodes) (closed : ClosedValues nodes)
    (memos : Memos) (valid : Valid before.heap memos) :
    ∃ saved, RowsReads actual memos saved ∧ Valid after.heap saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  cases actual with
  | @run edges heap rows after before reads tuples =>
      obtain ⟨middleMemo, exposed, coherent, retained, same⟩ := exposures_memos reads ready.semantic ready.costs
        available memos valid
      have own := reads.verified (SourceCurrentConjunctionEquality.FieldAvailable before.equality)
        ready.semantic ready.costs ready.fields available closed
      have middle : Ready (⟨heap, before.equality⟩ : Physical) :=
        ⟨own.1.semantic, own.1.costs, ready.valid, own.1.annotations⟩
      obtain ⟨saved, allocated, finalValid, finalRetained, finalSame⟩ := tuples_memos tuples middle
        (fun tuple member => (SourceCurrentConjunctionTuples.tuples_verified
          (SourceCurrentConjunctionEquality.FieldAvailable before.equality)
          reads ready.semantic ready.costs ready.fields available closed tuple member).2.1)
        (fun tuple member => (SourceCurrentConjunctionTuples.tuples_verified
          (SourceCurrentConjunctionEquality.FieldAvailable before.equality)
          reads ready.semantic ready.costs ready.fields available closed tuple member).2.2) middleMemo coherent
      exact ⟨saved, .run exposed allocated, finalValid, extends_trans retained finalRetained, finalSame.trans same⟩

/-- Actual worklist admissions derive all next memo premises without a future table invariant. -/
theorem run_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {budget : Nat} {table final : List (SourceCurrentConjunctionEmptinessTable.Entry (Value Symbol Guard))}
    {pending : List (List (Value Symbol Guard))} {before after : Physical}
    (actual : Run budget table pending before final after) (ready : Ready before)
    (available : PendingReady before pending) (memos : Memos) (valid : Valid before.heap memos) :
    ∃ saved, RunReads actual memos saved ∧ Valid after.heap saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  induction actual generalizing memos with
  | done => exact ⟨memos, .done, valid, extends_refl _, rfl⟩
  | empty impossible rest ih =>
      obtain ⟨saved, reads, coherent, retained, same⟩ := ih ready
        (fun nodes member => available nodes (List.mem_cons_of_mem _ member)) memos valid
      exact ⟨saved, .empty (impossible := impossible) reads, coherent, retained, same⟩
  | skip nonempty skipped rest ih =>
      obtain ⟨saved, reads, coherent, retained, same⟩ := ih ready
        (fun nodes member => available nodes (List.mem_cons_of_mem _ member)) memos valid
      exact ⟨saved, .skip (nonempty := nonempty) (skipped := skipped) reads, coherent, retained, same⟩
  | @admit budget table nodes before requirements middle pending final after nonempty fresh rows rest ih =>
      have admitted := SourceCurrentConjunctionEmptinessTable.admitted
        (SourceCurrentConjunctionRequirements.key : Value Symbol Guard → Int)
        SourceCurrentConjunctionWorklist.closed budget table nodes fresh
      have inputs := available nodes List.mem_cons_self
      have noFree := SourceCurrentConjunctionWorklist.closed_values nodes admitted.2.1
      have own := SourceCurrentConjunctionRowsSoundness.rows_verified rows ready inputs noFree
      obtain ⟨middleMemo, reads, coherent, retained, same⟩ := rows_memos rows ready inputs noFree memos valid
      have nextPending : PendingReady middle (requirements.flatten ++ pending) := by
        intro requirement member
        rcases List.mem_append.mp member with generated | earlier
        · obtain ⟨row, rowIn, requirementIn⟩ := List.mem_flatten.mp generated
          exact (own.2 row rowIn requirement requirementIn).1
        · exact SourceCurrentConjunctionWorklist.pending_keeps own.1.keeps
            (fun nodes member => available nodes (List.mem_cons_of_mem _ member)) requirement earlier
      obtain ⟨saved, suffix, finalValid, finalRetained, finalSame⟩ := ih own.1.ready nextPending middleMemo coherent
      exact ⟨saved, .admit (nonempty := nonempty) (fresh := fresh) reads suffix, finalValid, extends_trans retained finalRetained, finalSame.trans same⟩

/-- The current free guard and Boolean fixed point add no calls around the actual worklist. -/
theorem decision_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]
    {budget : Nat} {query : Value Symbol Guard} {before after : Physical} {answer : Bool}
    (actual : SourceCurrentConjunctionDecision.Decision budget query before answer after)
    (ready : Ready before) (available : Available before.heap query) (memos : Memos) (valid : Valid before.heap memos) :
    ∃ saved, DecisionReads actual memos saved ∧ Valid after.heap saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  cases actual with
  | open_input isOpen => exact ⟨memos, .open_input isOpen, valid, extends_refl _, rfl⟩
  | closed isClosed explored grown =>
      obtain ⟨saved, reads, coherent, retained, same⟩ := run_memos explored ready
        (by
          intro nodes member value included
          cases List.mem_singleton.mp member
          cases List.mem_singleton.mp included
          exact available) memos valid
      exact ⟨saved, .closed (isClosed := isClosed) (grown := grown) reads, coherent, retained, same⟩

/-- Actual current-body hits and misses derive coherent final global tables at the same returned heap. -/
theorem call_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]
    {budget : Nat} {memo saved : SourceCurrentEmptinessMemo.Memo} {query : Value Symbol Guard}
    {before after : Physical} {answer : Bool}
    (actual : SourceCurrentConjunctionMemo.Call budget memo query before answer after saved)
    (ready : Ready before) (available : Available before.heap query) (memos : Memos) (valid : Valid before.heap memos) :
    ∃ final, CallReads actual memos final ∧ Valid after.heap final ∧
      Extends memos.unfolding final.unfolding ∧ final.query = memos.query := by
  cases actual with
  | hit found => exact ⟨memos, .hit found, valid, extends_refl _, rfl⟩
  | miss absent decision =>
      obtain ⟨final, reads, coherent, retained, same⟩ := decision_memos decision ready available memos valid
      exact ⟨final, .miss (absent := absent) reads, coherent, retained, same⟩

end MicroCFTA.SourceCurrentConjunctionGlobalMemos
