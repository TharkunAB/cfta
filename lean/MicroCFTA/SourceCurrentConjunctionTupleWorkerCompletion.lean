import MicroCFTA.SourceCurrentConjunctionTupleWorkerEffects
import MicroCFTA.SourceCurrentConjunctionRowsWorkerCompletion

/-!
# Derived stable completion of physical tuple-budget exploration

Initial physical readiness supplies every reached exposure and tuple call.
Overflow and zero charge retain their exact exposure state. Positive charge
uses the complete fitting tuple list and its actual returned rows. The
worklist proof derives lower projection and read bounds at each reached
state. It does not assume a future row, heap, table, or completion callback.

The fixed-point bound comes from the completed table length. The selected
allocated caller still uses the earlier executor. Eager exposure and native
lazy demand remain separate boundaries.
-/
namespace MicroCFTA.SourceCurrentConjunctionTupleWorkerCompletion
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceCurrentConjunctionRowsAllocation (Ready Effects RowsReady)
open SourceCurrentConjunctionWorklist (PendingReady TableReady closed)
open SourceCurrentConjunctionWorker (Physical Table Outcome)
variable {Symbol Formula Output : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "key" => (SourceCurrentConjunctionRequirements.key : Node → Int)
local notation "isEmpty" => (SourceCurrentConjunctionRequirements.isEmpty : Node → Bool)

/-- All sufficiently large lower bounds return the same output and complete physical state. -/
def StableRun (evaluation : Nat → Nat → Outcome Symbol Formula Output) (output : Output)
    (after : Physical Symbol Formula) : Prop :=
  ∃ p h, ∀ P H, p ≤ P → h ≤ H → evaluation P H = .done output after

variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- Ready closed operands derive stable actual admission and every returned row invariant. -/
theorem admission_complete (budget : Nat) (nodes : List Node) (before : Physical Symbol Formula)
    (ready : Ready before) (available : Values before.heap nodes) (noFree : ClosedValues nodes) :
    ∃ result after,
      SourceCurrentConjunctionRowsWorkerCompletion.StableRun
        (fun p h => SourceCurrentConjunctionTupleAdmission.run p h budget nodes before) result after ∧
      Effects before after ∧
      (match result with
        | .positive _ rows => RowsReady after rows
        | _ => True) := by
  obtain ⟨edges, heap, reads, own, _resident⟩ :=
    SourceCurrentConjunctionCompletionReads.exposures_complete
      (SourceCurrentConjunctionEquality.FieldAvailable before.equality) nodes before.heap
      ready.semantic ready.costs ready.fields available noFree
  let exposed : Physical Symbol Formula := ⟨heap, before.equality⟩
  have kept : Effects before exposed :=
    ⟨own.keeps, ⟨own.semantic, own.costs, ready.valid, own.annotations⟩,
      SourceEqualityConstraintMemoAllocation.grows_refl _⟩
  obtain ⟨p, h, readDone⟩ :=
    SourceCurrentConjunctionRowsWorkerCompletion.exposures_complete reads before.equality
  by_cases overflow : budget < (SourceCurrentConjunctionTupleBudget.sample budget
      (SourceCurrentConjunctionTuples.tuples edges)).length
  · refine ⟨.overflow, exposed, ⟨p, h, ?_⟩, kept, trivial⟩
    intro P H enoughP enoughH
    exact SourceCurrentConjunctionTupleAdmission.run_overflow P H budget nodes before exposed edges
      (readDone P H enoughP enoughH) overflow
  · have fits := Nat.le_of_not_gt overflow
    have entire := SourceCurrentConjunctionTupleBudget.sample_eq_of_fits budget
      (SourceCurrentConjunctionTuples.tuples edges) fits
    cases sampled : SourceCurrentConjunctionTupleBudget.sample budget
        (SourceCurrentConjunctionTuples.tuples edges) with
    | nil =>
        refine ⟨.zero, exposed, ⟨p, h, ?_⟩, kept, trivial⟩
        intro P H enoughP enoughH
        exact SourceCurrentConjunctionTupleAdmission.run_zero P H budget nodes before exposed edges
          (readDone P H enoughP enoughH) sampled
    | cons first rest =>
        have full : SourceCurrentConjunctionTuples.tuples edges = first :: rest := entire.symm.trans sampled
        have data := SourceCurrentConjunctionTuples.tuples_verified
          (SourceCurrentConjunctionEquality.FieldAvailable before.equality)
          reads ready.semantic ready.costs ready.fields available noFree
        obtain ⟨rows, after, actual, later, returned⟩ :=
          SourceCurrentConjunctionRowsAllocation.tuples_complete
            (SourceCurrentConjunctionTuples.tuples edges) exposed kept.ready
            (fun tuple member => (data tuple member).2.1)
            (fun tuple member => (data tuple member).2.2)
            (fun tuple member => SourceCurrentConjunctionRowsAllocation.matching_arity tuple
              (SourceCurrentConjunctionTuples.tuples_matching edges tuple member))
        obtain ⟨laterP, laterH, tupleDone⟩ :=
          SourceCurrentConjunctionRowsWorkerCompletion.tuples_complete actual
        refine ⟨.positive rest.length rows, after,
          ⟨max p laterP, max h laterH, ?_⟩, kept.trans later, returned⟩
        intro P H enoughP enoughH
        apply SourceCurrentConjunctionTupleAdmission.run_positive P H budget nodes before exposed after edges first rest rows
          (readDone P H (by omega) (by omega)) sampled
        · simpa only [sampled, List.length_cons] using fits
        · simpa only [full] using tupleDone P H (by omega) (by omega)

/-- Initial readiness derives one stable successful worklist and its complete returned invariants. -/
theorem explore_complete (budget : Nat) (table : Table Symbol Formula) (pending : List (List Node))
    (before : Physical Symbol Formula) (ready : Ready before)
    (stored : TableReady before table) (available : PendingReady before pending) :
    ∃ final after,
      StableRun (fun p h => SourceCurrentConjunctionTupleWorker.explore p h budget table pending before) final after ∧
      Effects before after ∧ TableReady after final := by
  induction budget using Nat.strongRecOn generalizing table pending before with
  | ind budget smaller =>
      induction pending generalizing table before with
      | nil =>
          exact ⟨table, before, ⟨0, 0, by
            intro P H _ _
            exact SourceCurrentConjunctionTupleWorker.explore_nil P H budget table before⟩,
            Effects.refl before ready, stored⟩
      | cons nodes rest tail =>
          have tailAvailable : PendingReady before rest :=
            fun group member => available group (List.mem_cons_of_mem _ member)
          cases impossible : nodes.any isEmpty with
          | true =>
              obtain ⟨final, after, ⟨p, h, done⟩, kept, finalReady⟩ :=
                tail table before ready stored tailAvailable
              refine ⟨final, after, ⟨p, h, ?_⟩, kept, finalReady⟩
              intro P H enoughP enoughH
              exact (SourceCurrentConjunctionTupleWorker.explore_empty P H budget table nodes rest before impossible).trans
                (done P H enoughP enoughH)
          | false =>
              cases skipped : SourceCurrentConjunctionEmptinessTable.skip key closed budget table nodes with
              | true =>
                  obtain ⟨final, after, ⟨p, h, done⟩, kept, finalReady⟩ :=
                    tail table before ready stored tailAvailable
                  refine ⟨final, after, ⟨p, h, ?_⟩, kept, finalReady⟩
                  intro P H enoughP enoughH
                  exact (SourceCurrentConjunctionTupleWorker.explore_skip P H budget table nodes rest before
                    impossible skipped).trans (done P H enoughP enoughH)
              | false =>
                  have admitted := SourceCurrentConjunctionEmptinessTable.admitted key closed budget table nodes skipped
                  have inputs := available nodes List.mem_cons_self
                  have noFree := SourceCurrentConjunctionWorklist.closed_values nodes admitted.2.1
                  obtain ⟨result, middle, ⟨p, h, first⟩, kept, returned⟩ :=
                    admission_complete budget nodes before ready inputs noFree
                  have oldTable := SourceCurrentConjunctionWorklist.table_keeps kept.keeps stored
                  have oldPending := SourceCurrentConjunctionWorklist.pending_keeps kept.keeps tailAvailable
                  cases result with
                  | overflow =>
                      obtain ⟨final, after, ⟨laterP, laterH, done⟩, later, finalReady⟩ :=
                        smaller 0 admitted.1 table rest middle kept.ready oldTable oldPending
                      refine ⟨final, after, ⟨max p laterP, max h laterH, ?_⟩, kept.trans later, finalReady⟩
                      intro P H enoughP enoughH
                      exact (SourceCurrentConjunctionTupleWorker.explore_overflow P H budget table nodes rest before middle
                        impossible skipped (first P H (by omega) (by omega))).trans (done P H (by omega) (by omega))
                  | zero =>
                      have nextTable : TableReady middle (⟨nodes, []⟩ :: table) := by
                        intro entry member
                        rcases List.mem_cons.mp member with rfl | member
                        · exact ⟨fun value included => kept.keeps.available value (inputs value included), noFree,
                            impossible, by intro row absent; cases absent⟩
                        · exact oldTable entry member
                      obtain ⟨final, after, ⟨laterP, laterH, done⟩, later, finalReady⟩ :=
                        tail (⟨nodes, []⟩ :: table) middle kept.ready nextTable oldPending
                      refine ⟨final, after, ⟨max p laterP, max h laterH, ?_⟩, kept.trans later, finalReady⟩
                      intro P H enoughP enoughH
                      exact (SourceCurrentConjunctionTupleWorker.explore_zero P H budget table nodes rest before middle
                        impossible skipped (first P H (by omega) (by omega))).trans (done P H (by omega) (by omega))
                  | positive predecessor requirements =>
                      have charge := SourceCurrentConjunctionTupleAdmission.positive_charge p h budget nodes before middle
                        predecessor requirements (first p h (Nat.le_refl _) (Nat.le_refl _))
                      have nextTable : TableReady middle (⟨nodes, requirements⟩ :: table) := by
                        intro entry member
                        rcases List.mem_cons.mp member with rfl | member
                        · exact ⟨fun value included => kept.keeps.available value (inputs value included), noFree,
                            impossible, returned⟩
                        · exact oldTable entry member
                      have nextPending : PendingReady middle (requirements.flatten ++ rest) := by
                        intro group member
                        rcases List.mem_append.mp member with generated | earlier
                        · obtain ⟨row, present, included⟩ := List.mem_flatten.mp generated
                          exact (returned row present group included).1
                        · exact oldPending group earlier
                      obtain ⟨final, after, ⟨laterP, laterH, done⟩, later, finalReady⟩ :=
                        smaller (budget - (predecessor + 1)) (by omega)
                          (⟨nodes, requirements⟩ :: table) (requirements.flatten ++ rest) middle
                          kept.ready nextTable nextPending
                      refine ⟨final, after, ⟨max p laterP, max h laterH, ?_⟩, kept.trans later, finalReady⟩
                      intro P H enoughP enoughH
                      exact (SourceCurrentConjunctionTupleWorker.explore_positive P H budget table nodes rest before middle
                        predecessor requirements impossible skipped (first P H (by omega) (by omega))).trans
                        (done P H (by omega) (by omega))

/-- An empty initial table needs only actual pending operand availability. -/
theorem entered (budget : Nat) (pending : List (List Node)) (before : Physical Symbol Formula)
    (ready : Ready before) (available : PendingReady before pending) :
    ∃ final after,
      StableRun (fun p h => SourceCurrentConjunctionTupleWorker.explore p h budget [] pending before) final after ∧
      Effects before after ∧ TableReady after final :=
  explore_complete budget [] pending before ready (by intro entry absent; cases absent) available

/-- The actual final table supplies the complete fixed point and stable closed decision. -/
theorem decision_complete [DecidableEq (Value Symbol (SourceSymbolicIndex.Constraint Formula))]
    (budget : Nat) (start : Node) (before : Physical Symbol Formula)
    (ready : Ready before) (available : Available before.heap start) :
    ∃ answer after,
      StableRun (fun p h => SourceCurrentConjunctionTupleWorker.decision p h budget start before) answer after ∧
      Effects before after := by
  cases admitted : closed start with
  | false =>
      exact ⟨false, before, ⟨0, 0, by
        intro P H _ _
        exact SourceCurrentConjunctionTupleWorker.decision_open P H budget start before admitted⟩,
        Effects.refl before ready⟩
  | true =>
      have inputs : PendingReady before [[start]] := by
        intro nodes member value included
        cases List.mem_singleton.mp member
        cases List.mem_singleton.mp included
        exact available
      obtain ⟨table, after, ⟨p, h, done⟩, kept, _stored⟩ := entered budget [[start]] before ready inputs
      have grown := SourceCurrentConjunctionEmptinessTable.grow_rounds_complete .empty key closed table table.length 0
        (by omega)
      let known := ConservativeEmptiness.possible
        (SourceCurrentConjunctionEmptinessTable.states key table)
        (SourceCurrentConjunctionEmptinessTable.rows (.empty : Node) key closed table)
      let verdict := SourceCurrentConjunctionEmptinessTable.answer .empty key closed table known start
      refine ⟨verdict, after, ⟨p, h, ?_⟩, kept⟩
      intro P H enoughP enoughH
      exact SourceCurrentConjunctionTupleWorker.decision_closed_done P H budget start before after table known admitted
        (done P H enoughP enoughH) grown

local notation "ConcreteSymbol" => SourceObservations.Label FullSyntax.Formula
local notation "ConcreteGuard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "ConcreteNode" => Value ConcreteSymbol ConcreteGuard
local notation "Memo" => SourceCurrentEmptinessMemo.Memo

/-- Initial ready query state derives a stable successful call with the literal fourth-memo return. -/
theorem call_complete [DecidableEq ConcreteSymbol] [DecidableEq (EdgeKey ConcreteSymbol ConcreteGuard)]
    [DecidableEq ConcreteNode] (budget : Nat) (memo : Memo) (query : ConcreteNode)
    (before : Physical ConcreteSymbol FullSyntax.Formula) (ready : Ready before) (available : Available before.heap query) :
    ∃ answer after saved,
      StableRun (fun p h => SourceCurrentConjunctionTupleWorker.call p h budget memo query before) (answer, saved) after ∧
      Effects before after := by
  cases found : memo query.referenceOf with
  | some entry =>
      rcases entry with ⟨original, answer⟩
      exact ⟨answer, before, memo, ⟨0, 0, by
        intro P H _ _
        exact SourceCurrentConjunctionTupleWorker.call_hit P H budget memo query original before answer found⟩,
        Effects.refl before ready⟩
  | none =>
      obtain ⟨answer, after, ⟨p, h, done⟩, kept⟩ := decision_complete budget query before ready available
      refine ⟨answer, after, SourceCurrentEmptinessMemo.insert memo query answer, ⟨p, h, ?_⟩, kept⟩
      intro P H enoughP enoughH
      simp only [SourceCurrentConjunctionTupleWorker.call, found, done P H enoughP enoughH, Outcome.bind]

end MicroCFTA.SourceCurrentConjunctionTupleWorkerCompletion
