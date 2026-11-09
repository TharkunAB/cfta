import MicroCFTA.SourceCurrentAllocatedSharedConjunctionWorker
import MicroCFTA.SourceCurrentAllocatedSharedConjunctionWeakEffects
import MicroCFTA.SourceCurrentAllocatedSharedConjunctionGuardArity

/-!
# Effects of the lossless checked shared adapter

The literal adapter retains the exact shared outcome and private snapshot.
Its checked state and fourth memo follow that same outcome. Weak physical
effects need only the original semantic and closed-input premises. Current
caller invariants supply one ordered global bundle and the full Post on
every outcome. Annotation, causal guard observations and arity remain
separate predicates. This module does not change caller selection.
-/
namespace MicroCFTA.SourceCurrentAllocatedSharedConjunctionWorkerEffects
open Cache
open InternedConstructorTemplates (Value EdgeKey Grows)
open InternedRecordCoherence (Covered)
open InternedProbeProvenance (Available)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentConjunctionSharedWorkerOutcomeMemos (CallReads)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "AnnotationHeap" => SourceEqualityAnnotationHeap.Heap
local notation "call" => SourceCurrentAllocatedSharedConjunctionWorker.call
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width : Nat}

/-- Every checked outcome retains the original weak heap effects without readiness or costs. -/
theorem weak_effects (p h budget : Nat) (query : Node) (before : Checked width) (memo : Memo)
    (semantic : SemanticHeap before.native.machine.heap) (covered : Covered [] before.native.machine.heap)
    (available : Available before.native.machine.heap query) (closed : query.free = []) :
    let after := (call p h budget query before memo).state
    SemanticHeap after.native.machine.heap ∧ Covered [] after.native.machine.heap ∧
      Grows before.native.machine.heap after.native.machine.heap ∧
      Extends before.native.machine.heap.nodes.issued after.native.machine.heap.nodes.issued := by
  dsimp only
  rw [SourceCurrentAllocatedSharedConjunctionWorker.call_state,
    SourceCurrentAllocatedSharedConjunctionWorker.call_snapshot]
  exact SourceCurrentAllocatedSharedConjunctionWeakEffects.checked_effects
    p h budget memo query before semantic covered available closed

variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

/-- One actual adapter outcome retains one read bundle, full Post and three current heap invariants. -/
theorem verified {inventory : Inventory} (annotation causal : Guard → Prop) (p h budget : Nat)
    (before : Caller width) (query : Node) (memos : Memos)
    (initial : Context formulas solver inventory before memos)
    (available : Available before.checked.native.machine.heap query)
    (known : AnnotationHeap annotation before.checked.native.machine.heap)
    (guarded : SourceCurrentConstrainedCapGuardHeap.Heap causal before.checked.native.machine.heap)
    (arity : SourcePruningEnumerationArityOrigins.Heap before.checked.native.machine.heap) :
    let outcome := call p h budget query before.checked before.fourth
    ∃ final, CallReads p h budget before.fourth query (physical before.checked) memos final ∧
      Post formulas solver inventory before
        (SourceCurrentAllocatedPartialState.advance before outcome.state outcome.memo before.merge) final ∧
      AnnotationHeap annotation outcome.state.native.machine.heap ∧
      SourceCurrentConstrainedCapGuardHeap.Heap causal outcome.state.native.machine.heap ∧
      SourcePruningEnumerationArityOrigins.Heap outcome.state.native.machine.heap ∧
      Available outcome.state.native.machine.heap query ∧
      Extends memos.unfolding final.unfolding ∧ final.query = memos.query ∧
      (match outcome.raw with
       | .failed _ _ => True
       | .done result _ => SourceCurrentEmptinessMemo.AnswerSound formulas solver query result.1) := by
  have checked := SourceCurrentAllocatedSharedConjunctionGuardArity.verified formulas solver
    annotation causal p h budget before query memos initial available known guarded arity
  dsimp only at checked ⊢
  rw [SourceCurrentAllocatedSharedConjunctionWorker.call_state,
    SourceCurrentAllocatedSharedConjunctionWorker.call_snapshot,
    SourceCurrentAllocatedSharedConjunctionWorker.call_memo,
    SourceCurrentAllocatedSharedConjunctionWorker.call_observation]
  exact checked

end MicroCFTA.SourceCurrentAllocatedSharedConjunctionWorkerEffects
