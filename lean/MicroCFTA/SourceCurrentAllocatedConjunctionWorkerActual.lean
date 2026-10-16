import MicroCFTA.SourceCurrentAllocatedConjunctionWorker
import MicroCFTA.SourceCurrentConjunctionWorkerCompletion
import MicroCFTA.SourceCurrentConjunctionWorkerStability
import MicroCFTA.SourceCurrentAllocatedConjunctionCaller

/-!
# Literal current conjunction execution retains the full caller

A supplied literal success derives its exact current call and read receipts.
Initial Context and query residency construct sufficient stable bounds for
the actual interpreter. The same return retains both outer table families,
the merge table, the input inventory, and the sound fourth memo. True proves
emptiness. False has no acceptance claim. Global receipts remain logical
evidence rather than concrete host table execution.
-/
namespace MicroCFTA.SourceCurrentAllocatedConjunctionWorkerActual
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedConjunctionWorker
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Call" => SourceCurrentConjunctionMemo.Call
local notation "CallReads" => SourceCurrentConjunctionGlobalMemos.CallReads
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

/-- Larger lower-stage bounds preserve a supplied success and its whole checked state and fourth memo. -/
theorem call_done_stable {p h P H budget : Nat} {query : Value Symbol Guard} {before after : Checked width}
    {memo saved : Memo} {answer : Bool}
    (done : call p h budget query before memo = .done answer after saved) (enoughP : p ≤ P) (enoughH : h ≤ H) :
    call P H budget query before memo = .done answer after saved := by
  obtain ⟨reached, observed, rfl⟩ := call_done done
  exact call_lift (SourceCurrentConjunctionWorkerStability.call_done_stable observed enoughP enoughH)

/-- Different successful bounds identify the Boolean, every checked field, and the entire fourth memo. -/
theorem call_done_unique {p h P H budget : Nat} {query : Value Symbol Guard} {before after later : Checked width}
    {memo saved current : Memo} {answer other : Bool}
    (one : call p h budget query before memo = .done answer after saved)
    (two : call P H budget query before memo = .done other later current) :
    answer = other ∧ after = later ∧ saved = current := by
  have first := call_done_stable one (Nat.le_max_left p P) (Nat.le_max_left h H)
  have second := call_done_stable two (Nat.le_max_right p P) (Nat.le_max_right h H)
  exact Outcome.done.inj (first.symm.trans second)

/-- A supplied successful worker receives its own graph, reads, full caller, and conservative answer. -/
theorem verified {inventory : Inventory} {p h budget : Nat} {before : Caller width} {after : Checked width}
    {query : Value Symbol Guard} {answer : Bool} {saved : Memo} {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (available : Available before.checked.native.machine.heap query)
    (done : call p h budget query before.checked before.fourth = .done answer after saved) :
    ∃ reached final, after = advancePhysical before.checked reached ∧
      ∃ actual : Call budget before.fourth query (physical before.checked) answer reached saved,
        CallReads actual memos final ∧
        Post formulas solver inventory before
          (SourceCurrentAllocatedPartialState.advance before after saved before.merge) final ∧
        SourceCurrentEmptinessMemo.AnswerSound formulas solver query answer ∧
        Available after.native.machine.heap query ∧ Extends memos.unfolding final.unfolding ∧ final.query = memos.query := by
  obtain ⟨reached, observed, rfl⟩ := call_done done
  have actual := SourceCurrentConjunctionWorkerCompletion.call_sound p h budget before.fourth query
    (physical before.checked) answer reached saved observed
  obtain ⟨final, reads, post⟩ := SourceCurrentAllocatedConjunctionCaller.actual formulas solver actual initial available
  exact ⟨reached, final, rfl, actual, reads, post⟩

/-- Legitimate warm caller facts construct stable literal execution and its same full returned invariant. -/
theorem finite {inventory : Inventory} {before : Caller width} {query : Value Symbol Guard} {memos : Memos}
    (budget : Nat) (initial : Context formulas solver inventory before memos)
    (available : Available before.checked.native.machine.heap query) :
    ∃ answer after saved final p h,
      (∀ P H, p ≤ P → h ≤ H → call P H budget query before.checked before.fourth = .done answer after saved) ∧
      Post formulas solver inventory before
        (SourceCurrentAllocatedPartialState.advance before after saved before.merge) final ∧
      SourceCurrentEmptinessMemo.AnswerSound formulas solver query answer ∧ Available after.native.machine.heap query ∧
      Extends memos.unfolding final.unfolding ∧ final.query = memos.query := by
  obtain ⟨answer, after, saved, final, actual, _, post⟩ :=
    SourceCurrentAllocatedConjunctionCaller.finite formulas solver budget initial available
  obtain ⟨p, h, stable⟩ := SourceCurrentConjunctionWorkerCompletion.call_complete actual
  exact ⟨answer, advancePhysical before.checked after, saved, final, p, h,
    fun P H enoughP enoughH => call_lift (stable P H enoughP enoughH), post⟩

end MicroCFTA.SourceCurrentAllocatedConjunctionWorkerActual
