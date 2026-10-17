import MicroCFTA.SourceCurrentConstrainedCapCheckedJointClosed
import MicroCFTA.SourceCurrentAllocatedRecursiveWarmInitialRanges

/-!
# Finite warm checked calls with the same original source

Actual past receipts retain the source, contextual laws, and joint cell laws.
Initial query-entry counters derive all request words. The warm call keeps
its populated native tables and equality-operation cache. This theorem does
not rebase source-indexed laws to a different query source.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapCheckedJointWarm
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView IntersectSchedule SourceEqualityNativeDemand
open SourceCurrentAllocatedRecursivePrefixState (Current)
open SourceCurrentConstrainedCapKernelJoint (Context)
open SourceCurrentConstrainedCapCheckedJointClosed (Plain)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "DomainKey" => IntersectionFlatMemoKeyDomain.DomainKey
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Initial warm resources and actual past invariants construct a finite same-source joint return. -/
theorem warm_complete (bits depth : Nat) (source : InternedConstructorTemplates.State Symbol Guard)
    (facts : Facts source) (inventory : List DomainKey) (initialDomains : Cache.State DomainKey)
    (sourceClosed : SourceCurrentAllocatedRecursiveDomainCode.Closed source inventory)
    (emptyMember : IntersectionEmptyDomain.emptyDomain.key ∈ inventory)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inputModel : InputMeaning (view source (SourceEqualityPCSGuard.holds formulas solver)))
    (inputRanked : RankedInput (view source (SourceEqualityPCSGuard.holds formulas solver)) inputModel.valid)
    (before : Checked (bits + 2)) (current : Current source inventory initialDomains before)
    (context : Context Plain source before.native.machine)
    (stored : SourceCurrentConstrainedCapCheckedJointCache.Stored Plain source before.native)
    (contextual : SourceCurrentAllocatedNativeContextCache.Contextual
      (view source (SourceEqualityPCSGuard.holds formulas solver)) inputModel inputRanked
      (SourceEqualityPCSGuard.holds formulas solver) before.native)
    (idle : SourceRecursiveIntersectionNative.Idle before.native)
    (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available source left) (rightAvailable : Available source right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (leftCap : SourceCurrentConstrainedCap.Cap Plain depth left)
    (rightCap : SourceCurrentConstrainedCap.Cap Plain depth right)
    (nodes : before.native.machine.heap.nodes.next < 2 ^ bits)
    (edges : before.native.machine.heap.edges.next ≤ 2 ^ (bits + 2))
    (room : before.native.machine.domains.next +
      2 ^ (before.native.machine.heap.nodes.next +
        before.native.machine.heap.nodes.next * before.native.machine.heap.nodes.next) < 2 ^ (bits + 1)) :
    ∃ fuel value after,
      SourceCurrentAllocatedNativeContextualCompletion.Receipt
        (semanticView := view source (SourceEqualityPCSGuard.holds formulas solver)) (model := inputModel)
        (ranked := inputRanked) (semanticHolds := SourceEqualityPCSGuard.holds formulas solver)
        fuel (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before value after
        (fun final value => Available final.heap value)
        (fun _ value => SourceCurrentAllocatedNativeContextCache.NodeLaw
          (view source (SourceEqualityPCSGuard.holds formulas solver)) inputModel inputRanked
          (SourceEqualityPCSGuard.holds formulas solver) ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ value) ∧
      SourceCurrentConstrainedCapCheckedJointInduction.Return
        (source := source) (inventory := inventory) (initial := initialDomains) before after value
        (fun final value => Available final.heap value)
        (fun _ value => SourceCurrentConstrainedCapCheckedJointCode.NodeLaw Plain source
          ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ value) ∧
      SourceRecursiveIntersectionNative.Idle after.native ∧ value.free = [] ∧
      SourceCurrentConstrainedCap.Cap Plain depth value ∧
      SourceCurrentConstrainedCapPairOccurrences.Classified
        (SourceCurrentConstrainedCapPairOccurrences.sourceWeight Plain source)
        (SourceCurrentConstrainedCapNonplainRank.pairRank Plain left right) value ∧
      Original value ∧ SourceCurrentConstrainedCapNativeProbeSupport.ProbeFree value := by
  let holds := SourceEqualityPCSGuard.holds formulas solver
  let request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩
  have leftCurrent := leftAvailable.grows source before.native.machine.heap context.growth context.history
  have rightCurrent := rightAvailable.grows source before.native.machine.heap context.growth context.history
  have ranges := (SourceCurrentAllocatedRecursiveWarmInitialRanges.warm_initial_ranges bits before current.good current.semantic
    left right leftOriginal rightOriginal leftCurrent rightCurrent nodes edges room).1
  have complete := SourceRecursiveIntersectionRequestProgress.initial_complete source facts holds left right
    leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed
  have scope := initial_scope source left right leftOriginal rightOriginal leftAvailable rightAvailable
  have ready : NodeReady before.native.machine request := ⟨empty_domain _, leftCurrent, rightCurrent⟩
  obtain ⟨fuel, value, after, receipt⟩ := SourceCurrentAllocatedNativeContextualCompletion.request_complete source facts
    formulas solver inputModel inputRanked request scope complete before current.good contextual current.semantic ready
    context.growth context.history (idle.active _ holds _ before.native) ranges
  have physical := SourceCurrentAllocatedRecursivePrefixCode.request_node source inventory request before.native.machine ready scope emptyMember
  have certificate : SourceCurrentConstrainedCapCheckedJointControl.Certified Plain source
      (.code (requestNode request.domain left right)) before.native.machine
      (fun _ value => SourceCurrentConstrainedCapCheckedJointCode.NodeLaw Plain source request value) :=
    fun _ _ _ _ _ law => law
  have joint := SourceCurrentConstrainedCapCheckedJointTrace.completed facts sourceClosed fuel
    (.code (requestNode request.domain left right)) before after value _ _ current physical (fun _ => trivial)
    context certificate stored receipt.toReceipt.trace
  have inputs := SourceCurrentConstrainedCapOriginalSupport.closed_inputs source facts request.domain left right
    leftAvailable rightAvailable leftClosed rightClosed
  have law := joint.result depth (SourceCurrentConstrainedCapOriginalSupport.empty Plain source) inputs leftCap rightCap
  have closed := SourceRecursiveIntersectionResultScope.empty_scope value law.2.2
  have original := SourceRecursiveIntersectionOriginalOutput.closed_original value after.native.machine.heap
    joint.context.valid.1.coherent receipt.result closed
  have afterIdle := SourceCurrentAllocatedNativeRunning.done_idle (fuel + 1) _ before after value
    (by intro value; trivial) current.good.native.shape idle receipt.done
  exact ⟨fuel, value, after, receipt, joint, afterIdle, closed, law.1, law.2.1, original,
    SourceCurrentConstrainedCapNativeProbeSupport.of_closed value closed⟩

end MicroCFTA.SourceCurrentConstrainedCapCheckedJointWarm
