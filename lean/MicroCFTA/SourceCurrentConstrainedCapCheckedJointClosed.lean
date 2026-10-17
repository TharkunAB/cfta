import MicroCFTA.SourceCurrentConstrainedCapCheckedJointTrace
import MicroCFTA.SourceCurrentAllocatedRecursiveInitialRanges
import MicroCFTA.SourceRecursiveIntersectionOriginalOutput

/-!
# Finite checked recursive intersection from initial numeric resources

Initial counters derive request admission. The existing finite checked
execution supplies its own physical trace. Joint trace induction derives
cap, occurrence, and scope laws at that same complete returned state.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapCheckedJointClosed
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView IntersectSchedule SourceEqualityNativeDemand
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedRecursivePrefixState (Current)
open SourceCurrentConstrainedCapKernelJoint (Context)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- The actual source gate supplies the annotation used by each finite cap. -/
def Plain (guard : Guard) : Prop := SourceMemoGate.plain guard = true

/-- Initial numeric resources construct one finite checked return with every earlier receipt and its joint laws. -/
theorem cold_complete (bits depth : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (machine : Machine Symbol Guard) (operations : SourceEqualityConstraintMemoAllocation.State)
    (good : Good (⟨initial (bits + 2) machine, operations⟩ : Checked (bits + 2)))
    (semantic : SemanticReady machine.heap)
    (guards : SourceCurrentConstrainedCapGuardHeap.Heap Plain machine.heap)
    (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available machine.heap left) (rightAvailable : Available machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (leftCap : SourceCurrentConstrainedCap.Cap Plain depth left)
    (rightCap : SourceCurrentConstrainedCap.Cap Plain depth right)
    (nodes : machine.heap.nodes.next < 2 ^ bits) (edges : machine.heap.edges.next ≤ 2 ^ (bits + 2))
    (room : machine.domains.next + 2 ^ (machine.heap.nodes.next + machine.heap.nodes.next * machine.heap.nodes.next) <
      2 ^ (bits + 1)) :
    ∃ (inputModel : InputMeaning (view machine.heap (SourceEqualityPCSGuard.holds formulas solver)))
      (inputRanked : RankedInput (view machine.heap (SourceEqualityPCSGuard.holds formulas solver)) inputModel.valid)
      (fuel : Nat) (value : Value Symbol Guard) (after : Checked (bits + 2)),
      SourceCurrentAllocatedNativeContextualCompletion.Receipt
        (semanticView := view machine.heap (SourceEqualityPCSGuard.holds formulas solver)) (model := inputModel)
        (ranked := inputRanked) (semanticHolds := SourceEqualityPCSGuard.holds formulas solver)
        fuel (.code (requestNode IntersectionEmptyDomain.emptyDomain left right))
        ⟨initial (bits + 2) machine, operations⟩ value after
        (fun final value => Available final.heap value)
        (fun _ value => SourceCurrentAllocatedNativeContextCache.NodeLaw
          (view machine.heap (SourceEqualityPCSGuard.holds formulas solver)) inputModel inputRanked
          (SourceEqualityPCSGuard.holds formulas solver) ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ value) ∧
      SourceCurrentAllocatedNativeScopeCache.Scoped after.native ∧
      SourceRecursiveIntersectionNative.Idle after.native ∧ value.free = [] ∧
      (∀ output term, InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output value term ↔
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output left term ∧
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output right term) ∧
      Context Plain machine.heap after.native.machine ∧
      SourceCurrentConstrainedCapCheckedJointCache.Stored Plain machine.heap after.native ∧
      SourceCurrentConstrainedCap.Cap Plain depth value ∧
      SourceCurrentConstrainedCapPairOccurrences.Classified
        (SourceCurrentConstrainedCapPairOccurrences.sourceWeight Plain machine.heap)
        (SourceCurrentConstrainedCapNonplainRank.pairRank Plain left right) value ∧
      Original value ∧ SourceCurrentConstrainedCapNativeProbeSupport.ProbeFree value ∧
      Current machine.heap (SourceRecursiveIntersectionSourceInventory.domains machine.heap) machine.domains after := by
  obtain ⟨inputModel, inputRanked, fuel, value, after, receipt, scopedCache, idle, closed, meaning⟩ :=
    SourceCurrentAllocatedRecursiveInitialRanges.cold_complete bits formulas solver machine operations good semantic
      left right leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed nodes edges room
  let before : Checked (bits + 2) := ⟨initial (bits + 2) machine, operations⟩
  let inventory := SourceRecursiveIntersectionSourceInventory.domains machine.heap
  let request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩
  have facts := good.native.machine.1
  have sourceClosed := SourceCurrentAllocatedRecursiveDomainCode.source_closed machine.heap facts
  have current : Current machine.heap inventory machine.domains before :=
    SourceCurrentAllocatedRecursivePrefixState.initial machine.heap inventory before good semantic rfl
  have context : Context Plain machine.heap machine :=
    ⟨good.native.machine, semantic.ready.semantic, guards, grows_refl _, extends_refl _⟩
  have scope := initial_scope machine.heap left right leftOriginal rightOriginal leftAvailable rightAvailable
  have physical := SourceCurrentAllocatedRecursivePrefixCode.request_node machine.heap inventory request machine
    ⟨empty_domain machine, leftAvailable, rightAvailable⟩ scope
    (SourceRecursiveIntersectionSourceInventory.empty_mem machine.heap)
  have certificate : SourceCurrentConstrainedCapCheckedJointControl.Certified Plain machine.heap
      (.code (requestNode request.domain left right)) machine
      (fun _ result => SourceCurrentConstrainedCapCheckedJointCode.NodeLaw Plain machine.heap request result) :=
    fun _ _ _ _ _ law => law
  have joint := SourceCurrentConstrainedCapCheckedJointTrace.completed facts sourceClosed fuel
    (.code (requestNode request.domain left right)) before after value _ _ current physical (fun _ => trivial)
    context certificate (SourceCurrentConstrainedCapCheckedJointCache.initial_stored Plain machine.heap (bits + 2) machine)
    receipt.toReceipt.trace
  have inputs := SourceCurrentConstrainedCapOriginalSupport.closed_inputs machine.heap facts request.domain left right
    leftAvailable rightAvailable leftClosed rightClosed
  have law := joint.result depth (SourceCurrentConstrainedCapOriginalSupport.empty Plain machine.heap) inputs leftCap rightCap
  have original := SourceRecursiveIntersectionOriginalOutput.closed_original value after.native.machine.heap
    joint.context.valid.1.coherent receipt.result closed
  exact ⟨inputModel, inputRanked, fuel, value, after, receipt, scopedCache, idle, closed, meaning,
    joint.context, joint.stored, law.1, law.2.1, original,
    SourceCurrentConstrainedCapNativeProbeSupport.of_closed value closed, joint.current⟩

end MicroCFTA.SourceCurrentConstrainedCapCheckedJointClosed
