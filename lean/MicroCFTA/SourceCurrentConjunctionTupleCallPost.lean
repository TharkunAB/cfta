import MicroCFTA.SourceCurrentAllocatedTupleConjunctionWorker
import MicroCFTA.SourceCurrentConjunctionDemandMemo
import MicroCFTA.SourceCurrentConjunctionDemandWorklistEffects
import MicroCFTA.SourceCurrentConjunctionDemandWorklistEffects
import MicroCFTA.SourceCurrentAllocatedPartialInvariant
import MicroCFTA.SourceQueryUnfoldMemo

set_option autoImplicit false
open scoped Classical

/-!
# Caller preservation for every checked tuple-call outcome

The returned caller retains the supplied global memo bundle.
Successful calls retain their saved fourth memo. Failed calls retain the
original fourth memo and their reached physical state. The weak heap law
does not require equality-cache validity, costs, or full caller readiness.
-/
namespace MicroCFTA.SourceCurrentConjunctionTupleCallPost
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "ProbeHeap" => InternedFreshOrdinaryProbeHeap.Heap
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Every checked tuple outcome retains weak heap facts and issued identities. -/
theorem allocated_weak_effects {width : Nat} (p h budget : Nat) (memo : Memo)
    (query : Node) (before : Checked width)
    (semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap before.native.machine.heap)
    (covered : Covered [] before.native.machine.heap)
    (available : Available before.native.machine.heap query) (closed : query.free = []) :
    let actual := SourceCurrentAllocatedTupleConjunctionWorker.call p h budget query before memo
    SourceRecursiveIntersectionSemanticHeap.SemanticHeap actual.state.native.machine.heap ∧
      Covered [] actual.state.native.machine.heap ∧
      Grows before.native.machine.heap actual.state.native.machine.heap ∧
      Extends before.native.machine.heap.nodes.issued actual.state.native.machine.heap.nodes.issued := by
  cases Subsingleton.elim (inferInstance : DecidableEq (EdgeKey Symbol Guard))
    (fun a b => instDecidableEqEdgeKey a b)
  have beforeHeapEq : (physical before).heap = before.native.machine.heap := rfl
  have first := SourceCurrentConjunctionDemandWorklistEffects.weak_call_effects p h budget memo query
    (physical before) semantic covered available closed
  cases actual : SourceCurrentConjunctionDemandWorker.call p h budget memo query (physical before) with
  | done output after =>
      rcases output with ⟨answer, saved⟩
      have heapEq : (advancePhysical before after).native.machine.heap = after.heap :=
        congrArg (fun state : Physical => state.heap)
          (SourceCurrentAllocatedQueryMemo.physical_advance before after)
      simpa only [actual, SourceCurrentConjunctionWorker.Outcome.state,
        SourceCurrentAllocatedTupleConjunctionWorker.call,
        SourceCurrentAllocatedConjunctionWorker.Outcome.state, heapEq,
        beforeHeapEq] using first
  | failed fault after =>
      have heapEq : (advancePhysical before after).native.machine.heap = after.heap :=
        congrArg (fun state : Physical => state.heap)
          (SourceCurrentAllocatedQueryMemo.physical_advance before after)
      simpa only [actual, SourceCurrentConjunctionWorker.Outcome.state,
        SourceCurrentAllocatedTupleConjunctionWorker.call,
        SourceCurrentAllocatedConjunctionWorker.Outcome.state, heapEq,
        beforeHeapEq] using first

private theorem physical_post {width : Nat}
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory : Inventory}
    (before : Caller width) (after : Physical) (saved : Memo) (memos : Memos)
    (context : Context formulas solver inventory before memos)
    (effects : Effects (physical before.checked) after)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver after.heap saved)
    (probes : ProbeHeap after.heap) (retained : SourceCurrentEmptinessMemo.Extends before.fourth saved) :
    Post formulas solver inventory before
      (SourceCurrentAllocatedPartialState.advance before (advancePhysical before.checked after) saved before.merge) memos := by
  have receipt := SourceCurrentAllocatedConjunctionMemo.lift_effects before.checked after
    context.ready.good context.ready.idle effects
  have checked : Effects (physical before.checked) (physical (advancePhysical before.checked after)) := by
    simpa only [SourceCurrentAllocatedQueryMemo.physical_advance] using effects
  exact ⟨⟨SourceCurrentConjunctionClassScan.advance_ready before.checked after context.ready effects,
    context.admitted.advance after receipt.extension,
    context.sound.advance formulas solver _ saved before.merge checked,
    context.stored.grows effects.keeps, context.covered, correct,
    SourceQueryUnfoldMemo.valid_grows _ _ context.ready.semantic effects.keeps memos context.globals,
    probes⟩, checked, Cache.extends_refl _, retained⟩

/-- Every checked tuple-call outcome retains the original full caller and global memos. -/
theorem call_post {width : Nat}
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory : Inventory}
    (p h budget : Nat) (query : Node) (before : Caller width) (memos : Memos)
    (context : Context formulas solver inventory before memos)
    (available : Available before.checked.native.machine.heap query) (_closed : query.free = []) :
    let actual := SourceCurrentAllocatedTupleConjunctionWorker.call p h budget query before.checked before.fourth
    let after := SourceCurrentAllocatedPartialState.advance before actual.state actual.memo before.merge
    Post formulas solver inventory before after memos := by
  cases Subsingleton.elim (inferInstance : DecidableEq (EdgeKey Symbol Guard))
    (fun a b => instDecidableEqEdgeKey a b)
  have ready := SourceCurrentAllocatedConjunctionMemo.ready before.checked context.ready.good
    context.ready.semantic context.ready.costs
  have checked := SourceCurrentConjunctionDemandMemo.call_outcome formulas solver p h budget
    before.fourth query (physical before.checked) ready available context.correct
  have probes := SourceCurrentConjunctionDemandWorklistEffects.call_probes p h budget before.fourth
    query (physical before.checked) ready context.probes available
  cases actual : SourceCurrentConjunctionDemandWorker.call p h budget before.fourth query
      (physical before.checked) with
  | done output after =>
      rcases output with ⟨answer, saved⟩
      simp only [actual, SourceCurrentConjunctionWorker.Outcome.state,
        SourceCurrentConjunctionDemandMemo.OutcomeCorrect] at checked
      have clean : ProbeHeap after.heap := by
        simpa only [actual, SourceCurrentConjunctionWorker.Outcome.state] using probes
      have post := physical_post before after saved memos context checked.1 checked.2.1 clean checked.2.2.2
      simpa only [SourceCurrentAllocatedTupleConjunctionWorker.call, actual,
        SourceCurrentAllocatedConjunctionWorker.Outcome.state,
        SourceCurrentAllocatedConjunctionWorker.Outcome.memo] using post
  | failed fault after =>
      simp only [actual, SourceCurrentConjunctionWorker.Outcome.state,
        SourceCurrentConjunctionDemandMemo.OutcomeCorrect] at checked
      have clean : ProbeHeap after.heap := by
        simpa only [actual, SourceCurrentConjunctionWorker.Outcome.state] using probes
      have post := physical_post before after before.fourth memos context checked.1 checked.2 clean
        (fun _ _ found => found)
      simpa only [SourceCurrentAllocatedTupleConjunctionWorker.call, actual,
        SourceCurrentAllocatedConjunctionWorker.Outcome.state,
        SourceCurrentAllocatedConjunctionWorker.Outcome.memo] using post

end MicroCFTA.SourceCurrentConjunctionTupleCallPost
