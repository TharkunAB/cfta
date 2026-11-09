import MicroCFTA.SourceCurrentAllocatedSharedConjunctionWorker
import MicroCFTA.SourceCurrentAllocatedSharedConjunctionCompletion

/-!
# Complete checked shared calls with the same private snapshot

Successful replay retains the answer, complete checked state, fourth memo
and private snapshot. Current caller facts derive one stable success with
its actual ordered read receipt and full Post. The receipt belongs to the
derived base bounds. Larger bounds replay the same checked outcome.

These laws do not change a selected caller or give a resource forecast.
-/
namespace MicroCFTA.SourceCurrentAllocatedSharedConjunctionWorkerActual
open Cache
open InternedConstructorTemplates (Value EdgeKey)
open InternedProbeProvenance (Available)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentConjunctionSharedWorkerOutcomeMemos (CallReads)
open SourceCurrentAllocatedSharedConjunctionWorker
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Snapshot" => SourceCurrentConjunctionSharedWorklistStep.State Symbol FullSyntax.Formula
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "AnnotationHeap" => SourceEqualityAnnotationHeap.Heap
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

/-- Larger independent bounds retain the exact answer, checked state, fourth memo and private snapshot. -/
theorem call_done_stable {p h P H budget : Nat} {query : Node} {before after : Checked width}
    {memo saved : Memo} {answer : Bool} {snapshot : Snapshot}
    (actual : call p h budget query before memo = .done answer after saved snapshot)
    (enoughP : p ≤ P) (enoughH : h ≤ H) :
    call P H budget query before memo = .done answer after saved snapshot := by
  obtain ⟨observed, rfl⟩ := call_done actual
  exact call_lift (SourceCurrentConjunctionSharedWorkerStability.call_done_stable observed enoughP enoughH)

/-- Any two successful observations identify all four returned components. -/
theorem call_done_unique {p h P H budget : Nat} {query : Node} {before after later : Checked width}
    {memo saved current : Memo} {answer other : Bool} {snapshot next : Snapshot}
    (one : call p h budget query before memo = .done answer after saved snapshot)
    (two : call P H budget query before memo = .done other later current next) :
    answer = other ∧ after = later ∧ saved = current ∧ snapshot = next := by
  have first := call_done_stable one (Nat.le_max_left p P) (Nat.le_max_left h H)
  have second := call_done_stable two (Nat.le_max_right p P) (Nat.le_max_right h H)
  exact SourceCurrentAllocatedSharedConjunctionWorker.Outcome.done.inj (first.symm.trans second)

/-- A supplied checked success derives its own ordered reads, full Post and three returned heap invariants. -/
theorem verified {inventory : Inventory} (annotation causal : Guard → Prop)
    {p h budget : Nat} {before : Caller width} {after : Checked width} {query : Node}
    {answer : Bool} {saved : Memo} {snapshot : Snapshot} {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (available : Available before.checked.native.machine.heap query)
    (known : AnnotationHeap annotation before.checked.native.machine.heap)
    (guarded : SourceCurrentConstrainedCapGuardHeap.Heap causal before.checked.native.machine.heap)
    (arity : SourcePruningEnumerationArityOrigins.Heap before.checked.native.machine.heap)
    (actual : call p h budget query before.checked before.fourth = .done answer after saved snapshot) :
    ∃ final, CallReads p h budget before.fourth query (physical before.checked) memos final ∧
      Post formulas solver inventory before
        (SourceCurrentAllocatedPartialState.advance before after saved before.merge) final ∧
      AnnotationHeap annotation after.native.machine.heap ∧
      SourceCurrentConstrainedCapGuardHeap.Heap causal after.native.machine.heap ∧
      SourcePruningEnumerationArityOrigins.Heap after.native.machine.heap ∧
      SourceCurrentEmptinessMemo.AnswerSound formulas solver query answer ∧
      Available after.native.machine.heap query ∧
      Extends memos.unfolding final.unfolding ∧ final.query = memos.query := by
  obtain ⟨observed, rfl⟩ := call_done actual
  have checked := SourceCurrentAllocatedSharedConjunctionGuardArity.verified formulas solver
    annotation causal p h budget before query memos initial available known guarded arity
  dsimp only at checked
  rw [observed] at checked
  dsimp only [SourceCurrentConjunctionSharedWorker.Outcome.state,
    SourceCurrentConjunctionSharedWorkerOutcomeMemos.returnedMemo] at checked
  obtain ⟨final, reads, post, annotations, causalKept, arityKept, resident, retained, same, sound⟩ := checked
  exact ⟨final, reads, post, annotations, causalKept, arityKept, sound, resident, retained, same⟩

/-- Full current caller facts derive stable checked completion with the same base reads and private endpoint. -/
theorem finite {inventory : Inventory} (annotation causal : Guard → Prop) (budget : Nat)
    (before : Caller width) (query : Node) (memos : Memos)
    (initial : Context formulas solver inventory before memos)
    (available : Available before.checked.native.machine.heap query)
    (known : AnnotationHeap annotation before.checked.native.machine.heap)
    (guarded : SourceCurrentConstrainedCapGuardHeap.Heap causal before.checked.native.machine.heap)
    (arity : SourcePruningEnumerationArityOrigins.Heap before.checked.native.machine.heap) :
    ∃ (p h : Nat) (answer : Bool) (after : Checked width) (saved : Memo) (snapshot : Snapshot) (final : Memos),
      call p h budget query before.checked before.fourth = .done answer after saved snapshot ∧
      CallReads p h budget before.fourth query (physical before.checked) memos final ∧
      Post formulas solver inventory before
        (SourceCurrentAllocatedPartialState.advance before after saved before.merge) final ∧
      AnnotationHeap annotation after.native.machine.heap ∧
      SourceCurrentConstrainedCapGuardHeap.Heap causal after.native.machine.heap ∧
      SourcePruningEnumerationArityOrigins.Heap after.native.machine.heap ∧
      SourceCurrentEmptinessMemo.AnswerSound formulas solver query answer ∧
      Available after.native.machine.heap query ∧
      Extends memos.unfolding final.unfolding ∧ final.query = memos.query ∧
      (∀ P H, p ≤ P → h ≤ H →
        call P H budget query before.checked before.fourth = .done answer after saved snapshot) := by
  obtain ⟨p, h, answer, saved, snapshot, final, actual, reads, post, annotations, causalKept,
      arityKept, sound, resident, retained, same, stable⟩ :=
    SourceCurrentAllocatedSharedConjunctionCompletion.finite formulas solver annotation causal
      budget before query memos initial available known guarded arity
  exact ⟨p, h, answer, advancePhysical before.checked snapshot.storage.requirements.physical, saved,
    snapshot, final, call_lift actual, reads, post, annotations, causalKept, arityKept, sound, resident,
    retained, same, fun _ _ enoughP enoughH => call_lift (stable _ _ enoughP enoughH)⟩

end MicroCFTA.SourceCurrentAllocatedSharedConjunctionWorkerActual
