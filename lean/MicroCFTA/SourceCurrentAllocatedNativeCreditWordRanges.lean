import MicroCFTA.SourceCurrentAllocatedNativeFuelWordRanges
import MicroCFTA.SourceCurrentAllocatedNativeInstructionTrace
import MicroCFTA.SourceCurrentAllocatedNativeObservedWords

/-!
# Native word admission from initial semantic instruction credit

Every raw earlier spends the initial source instruction credit. The proof
first checks its shorter earlier. It then charges its actual last step.
Domain capacity uses that initial credit. It does not use the cardinality
of the finite domain inventory or assume a completed physical trace.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeCreditWordRanges
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView IntersectSchedule SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativeInstructionTrace (nodeBudget)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem raw_last {A : Type} {width count : Nat} {control next : Control A}
    {before after : Checked width} (actual : Steps (count + 1) control before next after) :
    ∃ middle current, Steps count control before middle current ∧ step middle current = .yielded next after := by
  induction count generalizing control before with
  | zero =>
      cases actual with
      | cons control before middle current next after count one rest =>
          cases rest
          exact ⟨control, before, .refl _ _, one⟩
  | succ count ih =>
      cases actual with
      | cons control before middle current next after fuel one rest =>
          obtain ⟨last, state, earlier, final⟩ := ih rest
          exact ⟨last, state, .cons _ _ _ _ _ _ _ one earlier, final⟩

/-- Initial semantic credit admits the words of every actual raw earlier. -/
theorem word_ranges (bits : Nat) (holds : Guard → Language.Term Symbol → Bool)
    (before : Checked (bits + 2)) (good : Good before)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before.native.machine.heap)
    (left right : Value Symbol Guard) (leftAvailable : Available before.native.machine.heap left)
    (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (nodes : before.native.machine.heap.nodes.next < 2 ^ bits)
    (edges : before.native.machine.heap.edges.next ≤ 2 ^ (bits + 2))
    (room : before.native.machine.domains.next + nodeBudget before.native.machine.heap holds
      ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ < 2 ^ (bits + 1)) :
    SourceCurrentAllocatedNativeRequestBounds.WordRanges
      (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before := by
  let source := before.native.machine.heap
  let request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩
  let bound := nodeBudget source holds request
  have facts := good.native.machine.1
  have leftOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original left source facts.coherent leftAvailable leftClosed
  have rightOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original right source facts.coherent rightAvailable rightClosed
  have scope := initial_scope source left right leftOriginal rightOriginal leftAvailable rightAvailable
  have complete : Completes (view source holds) (SourceRecursiveIntersectionNative.nodeSemantic request) :=
    SourceRecursiveIntersectionRequestProgress.initial_complete source facts holds left right
    leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed
  have ready : NodeReady before.native.machine request := ⟨empty_domain _, leftAvailable, rightAvailable⟩
  have charged : SourceRecursiveIntersectionInstructionCredit.NodeCharge source holds
      (SourceRecursiveIntersectionInstructionProfile.sourceBranching source) request bound := by
    refine ⟨scope, complete, ?_⟩
    dsimp only [bound]
    rw [SourceCurrentAllocatedNativeInstructionTrace.nodeBudget_of_complete source holds request complete]
    exact Nat.le_refl _
  have certificate := SourceRecursiveIntersectionInstructionCredit.request_node request before.native.machine bound ready charged
  have counted : ∀ count next after,
      Steps count (.code (requestNode request.domain request.left request.right)) before next after → count ≤ bound := by
    intro count
    induction count with
    | zero => intro next after actual; exact Nat.zero_le _
    | succ count ih =>
        intro next after actual
        obtain ⟨middle, current, earlier, last⟩ := raw_last actual
        have within := ih middle current earlier
        have receipt := SourceCurrentAllocatedNativeFuelWordRanges.node_prefix bits bound before good semantic
          left right leftAvailable rightAvailable leftClosed rightClosed nodes edges room within earlier
        obtain ⟨remaining, spent, retained⟩ := SourceCurrentAllocatedNativeInstructionTrace.prefix_bound
          source facts holds receipt.trace good (fun _ => trivial) (grows_refl _) (extends_refl _) certificate
        obtain ⟨rest, consumed, _⟩ := SourceCurrentAllocatedNativeInstructionStep.yielded source facts holds
          middle next current after remaining (fun final value => Available final.heap value)
          receipt.current.good receipt.inputs receipt.fields receipt.current.growth receipt.current.history retained last
        omega
  intro count next after actual
  have receipt := SourceCurrentAllocatedNativeFuelWordRanges.node_prefix bits bound before good semantic
    left right leftAvailable rightAvailable leftClosed rightClosed nodes edges room (counted count next after actual) actual
  exact SourceCurrentAllocatedNativeObservedWords.inputs_words next after receipt.inputs

end MicroCFTA.SourceCurrentAllocatedNativeCreditWordRanges
