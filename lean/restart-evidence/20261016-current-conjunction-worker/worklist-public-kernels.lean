import MicroCFTA.SourceCurrentConjunctionWorkerCompletion
import MicroCFTA.SourceCurrentConjunctionWorkerStability

namespace MicroCFTA.CurrentConjunctionWorkerChecks
open InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentConjunctionWorker
open SourceCurrentConjunctionWorkerCompletion
open SourceCurrentConjunctionWorkerStability
open SourceCurrentConjunctionWorklist (closed)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "key" => (SourceCurrentConjunctionRequirements.key : Value Symbol Guard → Int)
local notation "isEmpty" => (SourceCurrentConjunctionRequirements.isEmpty : Value Symbol Guard → Bool)
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

-- Exhausted admission budget drains every queued item without row reads or state changes.
example (p h : Nat) (table : Table Symbol FullSyntax.Formula)
    (pending : List (List (Value Symbol Guard))) (before : Physical Symbol FullSyntax.Formula) :
    explore p h 0 table pending before = .done table before := by
  induction pending with
  | nil => rw [explore.eq_def]
  | cons nodes rest ih =>
      rw [explore.eq_def]
      cases impossible : nodes.any isEmpty <;>
        simp only [impossible, ite_true, Bool.false_eq_true, ite_false,
          SourceCurrentConjunctionEmptinessTable.skip, beq_self_eq_true, Bool.true_or, ih]

-- A literal cache hit precedes the open guard. The deliberately unverified cache has no semantic claim.
example (name : InternedBinderProtocol.Reference) (before : Physical Symbol FullSyntax.Formula) (budget : Nat) :
    let query : Value Symbol Guard := .reference name
    let memo := SourceCurrentEmptinessMemo.insert SourceCurrentEmptinessMemo.empty query true
    decision 0 0 budget query before = .done false before ∧
      call 0 0 budget memo query before = .done (true, memo) before := by
  simp [decision, closed, Value.free, call, SourceCurrentEmptinessMemo.insert]

-- A cold open miss completes at zero lower-stage bounds and saves the original record with false.
example (name : InternedBinderProtocol.Reference) (before : Physical Symbol FullSyntax.Formula) (budget : Nat) :
    let query : Value Symbol Guard := .reference name
    call 0 0 budget SourceCurrentEmptinessMemo.empty query before =
      .done (false, SourceCurrentEmptinessMemo.insert SourceCurrentEmptinessMemo.empty query false) before := by
  simp only [call, SourceCurrentEmptinessMemo.empty, decision, closed, Value.free,
    List.isEmpty_cons, Bool.false_eq_true, ite_false, Outcome.bind]

-- Closed Empty needs no row read even with budget zero, and the literal fixed point certifies true.
example (p h : Nat) (before : Physical Symbol FullSyntax.Formula) :
    decision p h 0 (.empty : Value Symbol Guard) before = .done true before := by
  simp [decision, closed, Value.free, explore.eq_def, SourceCurrentConjunctionRequirements.isEmpty,
    SourceCurrentConjunctionEmptinessTable.grow, SourceCurrentConjunctionEmptinessTable.same,
    SourceCurrentConjunctionEmptinessTable.states, Outcome.bind,
    SourceCurrentConjunctionEmptinessTable.answer, SourceCurrentConjunctionEmptinessTable.canAccept]

-- A failed admitted row retains its exact reached table, pending queue, and returned operations.
example (p h budget : Nat) (table : Table Symbol FullSyntax.Formula)
    (nodes : List (Value Symbol Guard)) (rest : List (List (Value Symbol Guard)))
    (before after : Physical Symbol FullSyntax.Formula) (fault : SourceCurrentConjunctionRowsWorker.Fault)
    (nonempty : nodes.any isEmpty = false)
    (fresh : SourceCurrentConjunctionEmptinessTable.skip key closed budget table nodes = false)
    (failed : SourceCurrentConjunctionRowsWorker.rows p h nodes before = .failed fault after) :
    explore p h budget table (nodes :: rest) before = .failed (.rows fault table (nodes :: rest)) after := by
  rw [explore.eq_def]
  simp only [nonempty, Bool.false_eq_true, ite_false, fresh, failed]

-- Initial physical and memo facts construct an actual finite success with sound retained answers.
example (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (budget : Nat) (memo : Memo)
    (query : Value Symbol Guard) (before : Physical Symbol FullSyntax.Formula)
    (ready : SourceCurrentConjunctionRowsAllocation.Ready before) (available : Available before.heap query)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.heap memo) :
    ∃ p h answer after saved,
      call p h budget memo query before = .done (answer, saved) after ∧
      SourceCurrentEmptinessMemo.Correct formulas solver after.heap saved ∧
      SourceCurrentEmptinessMemo.AnswerSound formulas solver query answer ∧
      SourceCurrentEmptinessMemo.Extends memo saved := by
  obtain ⟨answer, after, saved, stable, actual, _⟩ := call_finite budget memo query before ready available
  obtain ⟨p, h, returns⟩ := stable
  have result := SourceCurrentConjunctionMemo.verified formulas solver actual ready available correct
  exact ⟨p, h, answer, after, saved, returns p h (Nat.le_refl _) (Nat.le_refl _), result.2⟩

-- Different successful lower-stage bounds identify the answer, constructor heap, operation cache, and memo.
example {p h P H budget : Nat} {memo saved current : Memo} {query : Value Symbol Guard}
    {before after later : Physical Symbol FullSyntax.Formula} {first second : Bool}
    (one : call p h budget memo query before = .done (first, saved) after)
    (two : call P H budget memo query before = .done (second, current) later) :
    first = second ∧ after.heap = later.heap ∧ after.equality = later.equality ∧ saved = current := by
  obtain ⟨answers, states, memos⟩ := call_done_unique one two
  cases states
  exact ⟨answers, rfl, rfl, memos⟩

end MicroCFTA.CurrentConjunctionWorkerChecks
