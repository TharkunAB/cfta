import MicroCFTA.SourceCurrentConstrainedCapKernelJointExecution
import MicroCFTA.SourceRecursiveIntersectionNativeResultScope
import MicroCFTA.SourceRecursiveIntersectionOriginalOutput

/-!
# Joint cap laws at the same finite native return

Exact native meaning supplies the actual bounded source call and its machine.
The source producer derives cap, occurrence, and scope laws for that return.
Closed initial operands construct their own finite cold native execution.
The existing word-range premise remains explicit for this generic worker.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapNativeJointClosed
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedRecordCoherence
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceCurrentConstrainedCap (Cap)
open SourceCurrentConstrainedCapNativeOccurrenceCache (OriginalBindings NodeInputs)
open SourceCurrentConstrainedCapPairOccurrences (Classified sourceWeight)
open SourceCurrentConstrainedCapNonplainRank (pairRank)
open SourceRecursiveIntersectionResultScope (Scope)
open SourceRecursiveIntersectionInputView (Original)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceCurrentConstrainedCapKernelJoint (Context)
variable {Symbol Guard : Type}

/-- Exact native meaning transfers the proved source laws to its identical returned machine. -/
theorem request_joint [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) (source : State Symbol Guard) (facts : Facts source)
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (emptyValid : annotation emptyGuard)
    (conjoinValid : ∀ first second, annotation first → annotation second → annotation (conjoin first second))
    (depth : Nat) (request : NodeRequest Symbol Guard) (before after : Machine Symbol Guard) (value : Value Symbol Guard)
    (meaning : SourceRecursiveIntersectionNative.Meaning emptyGuard conjoin (.node request .pure) before value after)
    (context : Context annotation source before) (known : Domain before request.domain)
    (bindings : OriginalBindings annotation source request.domain.key) (inputs : NodeInputs source request)
    (leftCap : Cap annotation depth request.left) (rightCap : Cap annotation depth request.right) :
    Context annotation source after ∧ Available after.heap value ∧ Cap annotation depth value ∧
      Classified (sourceWeight annotation source) (pairRank annotation request.left request.right) value ∧
      Scope request.domain.key.seen value := by
  obtain ⟨fuel, repeated⟩ := meaning
  have actual := repeated 0
  change (SourceRecursiveIntersectionKernel.execute emptyGuard conjoin (fuel + 0)
    request.domain request.left request.right before).bind (fun value after => .done value after) = .done value after at actual
  rw [Nat.add_zero, SourceRecursiveIntersectionCode.result_bind_pure] at actual
  exact SourceCurrentConstrainedCapKernelJoint.execute_joint annotation source facts emptyGuard conjoin emptyValid conjoinValid fuel
    depth request.domain request.left request.right before context known bindings inputs leftCap rightCap value after actual

/-- A supplied actual warm return derives joint laws from physical provenance and current inputs. -/
theorem done_joint_of_ranges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) (source : State Symbol Guard) (facts : Facts source)
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (emptyValid : annotation emptyGuard)
    (conjoinValid : ∀ first second, annotation first → annotation second → annotation (conjoin first second))
    (depth : Nat) (request : NodeRequest Symbol Guard)
    (before after : SourceRecursiveIntersectionThunks.State width Symbol Guard) (value : Value Symbol Guard)
    (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin before)
    (context : Context annotation source before.machine) (known : Domain before.machine request.domain)
    (bindings : OriginalBindings annotation source request.domain.key) (inputs : NodeInputs source request)
    (leftCap : Cap annotation depth request.left) (rightCap : Cap annotation depth request.right)
    (ranges : SourceRecursiveIntersectionNative.WordRanges emptyGuard conjoin (.node request .pure) before)
    (fuel : Nat) (done : SourceRecursiveIntersectionNative.execute emptyGuard conjoin fuel (.node request .pure) before = .done value after) :
    SourceRecursiveIntersectionNative.Correct emptyGuard conjoin (.node request .pure) before value after
      (fun final value => Available final.heap value) ∧
    Context annotation source after.machine ∧ Available after.machine.heap value ∧ Cap annotation depth value ∧
      Classified (sourceWeight annotation source) (pairRank annotation request.left request.right) value ∧
      Scope request.domain.key.seen value := by
  have ready : NodeReady before.machine request := ⟨known,
    inputs.2.2.1.grows source before.machine.heap context.growth context.history,
    inputs.2.2.2.1.grows source before.machine.heap context.growth context.history⟩
  have correct := SourceRecursiveIntersectionNative.done_correct_of_ranges emptyGuard conjoin (.node request .pure)
    before after value (fun final value => Available final.heap value) (by intro value; trivial)
    (SourceRecursiveIntersectionCode.safe_requestNode request.domain request.left request.right before.machine ready)
    valid ranges fuel done
  exact ⟨correct, request_joint annotation source facts emptyGuard conjoin emptyValid conjoinValid depth request
    before.machine after.machine value correct.meaning context known bindings inputs leftCap rightCap⟩

/-- Closed initial inputs construct a finite native return with the entire earlier receipt and its joint laws. -/
theorem cold_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) (depth : Nat) (source : State Symbol Guard)
    (semantic : SemanticHeap source) (covered : Covered [] source)
    (guards : SourceCurrentConstrainedCapGuardHeap.Heap annotation source)
    (domains : Cache.State DomainKey) (domainsValid : Cache.Valid domains)
    (holds : Guard → Language.Term Symbol → Bool) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (emptyValid : annotation emptyGuard)
    (conjoinValid : ∀ first second, annotation first → annotation second → annotation (conjoin first second))
    (left right : Value Symbol Guard) (leftAvailable : Available source left) (rightAvailable : Available source right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (leftCap : Cap annotation depth left) (rightCap : Cap annotation depth right)
    (ranges : SourceRecursiveIntersectionNative.WordRanges emptyGuard conjoin
      (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure)
      (initial width ⟨source, domains⟩)) :
    ∃ fuel value after,
      SourceRecursiveIntersectionNative.execute emptyGuard conjoin fuel
        (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure)
        (initial width ⟨source, domains⟩) = .done value after ∧
      SourceRecursiveIntersectionNative.Correct emptyGuard conjoin
        (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure)
        (initial width ⟨source, domains⟩) value after (fun final value => Available final.heap value) ∧
      SemanticHeap after.machine.heap ∧ Covered [] after.machine.heap ∧
      (∀ extra, SourceRecursiveIntersectionNative.execute emptyGuard conjoin (fuel + extra)
        (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure)
        (initial width ⟨source, domains⟩) = .done value after) ∧
      Context annotation source after.machine ∧ Cap annotation depth value ∧
      Classified (sourceWeight annotation source) (pairRank annotation left right) value ∧
      value.free = [] ∧ Original value ∧ SourceCurrentConstrainedCapNativeProbeSupport.ProbeFree value := by
  let request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩
  let machine : Machine Symbol Guard := ⟨source, domains⟩
  have inputs := SourceCurrentConstrainedCapOriginalSupport.closed_inputs source semantic.1.normal.facts
    request.domain left right leftAvailable rightAvailable leftClosed rightClosed
  obtain ⟨fuel, value, after, done, correct, finalSemantic, finalCovered, stable⟩ :=
    SourceRecursiveIntersectionNative.cold_node_complete source semantic covered domains domainsValid holds emptyGuard conjoin
      left right inputs.1 inputs.2.1 leftAvailable rightAvailable leftClosed rightClosed ranges
  have context : Context annotation source machine :=
    ⟨⟨semantic.1.normal.facts, domainsValid⟩, semantic, guards, grows_refl _, extends_refl _⟩
  have joint := request_joint annotation source semantic.1.normal.facts emptyGuard conjoin emptyValid conjoinValid depth
    request machine after.machine value correct.meaning context (empty_domain machine)
    (SourceCurrentConstrainedCapOriginalSupport.empty annotation source) inputs leftCap rightCap
  have closed := SourceRecursiveIntersectionResultScope.empty_scope value joint.2.2.2.2
  exact ⟨fuel, value, after, done, correct, finalSemantic, finalCovered, stable,
    joint.1, joint.2.2.1, joint.2.2.2.1, closed, correct.closed_original closed,
    SourceCurrentConstrainedCapNativeProbeSupport.of_closed value closed⟩

end MicroCFTA.SourceCurrentConstrainedCapNativeJointClosed
