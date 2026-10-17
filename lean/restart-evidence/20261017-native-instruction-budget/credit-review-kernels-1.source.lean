import MicroCFTA.SourceRecursiveIntersectionInstructionCredit
import MicroCFTA.InternedFreshOrdinaryClosedCompletion
import MicroCFTA.SourceRecursiveIntersectionOriginalOutput

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace MicroCFTA.CreditReviewKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView IntersectSchedule
open SourceRecursiveIntersectionInstructionCredit
open InternedNestedConstruction (Syntax Outcome)
local notation "Credit" => SourceRecursiveIntersectionInstructionCredit.At

private def expression : Syntax Nat Bool := .binder false (.var 0)
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def original : Value Nat Bool := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def machine : Machine Nat Bool := ⟨heap, Cache.emptyState⟩
private def request : NodeRequest Nat Bool := ⟨IntersectionEmptyDomain.emptyDomain, original, original⟩
private def start := initial 8 machine
private def running := (demandNode 0 (lookupNode 8 request start).2).2
private def finished := finishNode 0 original running
private def holds (_ : Bool) (_ : Language.Term Nat) := true
private def limit := SourceRecursiveIntersectionInstructionProfile.sourceBranching heap

private theorem constructed : built = .done original heap := by
  obtain ⟨value, final, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  simp only [built, original, heap, done, Outcome.state]
private theorem facts : Facts heap := (InternedFreshOrdinaryFacts.closed_verified expression).facts
private theorem available : Available heap original := (InternedFreshOrdinaryFacts.closed_verified expression).result _ _ constructed
private theorem closed : original.free = [] :=
  InternedFreshOrdinarySourceFreeNames.closed_free_empty expression original heap constructed
private theorem original_input : Original original :=
  SourceRecursiveIntersectionOriginalOutput.closed_original original heap facts.coherent available closed
private theorem semantic_complete : Completes (view heap holds) (SourceRecursiveIntersectionNative.nodeSemantic request) :=
  SourceRecursiveIntersectionRequestProgress.initial_complete heap facts holds original original
    original_input original_input available available closed closed
private noncomputable def amount := SourceRecursiveIntersectionInstructionProfile.budget limit
  (requiredFuel (view heap holds) (SourceRecursiveIntersectionNative.nodeSemantic request) semantic_complete)
private theorem charged : NodeCharge heap holds limit request amount :=
  ⟨initial_scope heap original original original_input original_input available available, semantic_complete, Nat.le_refl _⟩
private theorem valid : SourceRecursiveIntersectionKernel.Valid machine := ⟨facts, Cache.empty_valid⟩
private theorem ready : NodeReady machine request := ⟨empty_domain machine, available, available⟩
private theorem running_machine : running.machine = machine := by cbv
private theorem body : compileNode request = .pure original := by cbv

/-- Actual cold source publication exposes its exact owner and finish; initial semantic credit pays both steps and the final pure return is separate. -/
theorem actual_owner_credit :
    built = .done original heap ∧
    NodeCharge heap holds limit request amount ∧
    Credit heap holds limit (requestNode request.domain request.left request.right) machine amount
      (fun after value => Available after.heap value) ∧
    running.nodes.cells 0 = some ⟨request, .evaluating⟩ ∧
    Credit heap holds limit ((compileNode request).bind (fun value => .finishNode 0 value (.pure value)))
      running.machine 1 (fun after value => Available after.heap value) ∧
    SourceRecursiveIntersectionNative.execute false (fun first second => first && second) 3
      (requestNode request.domain request.left request.right) start = .done original finished ∧
    finished.nodes.cells 0 = some ⟨request, .returned original⟩ ∧ 1 + 1 ≤ amount := by
  have requestCredit := request_node request machine amount ready charged
  have bodyCredit : Credit heap holds limit (compileNode request) running.machine 0
      (fun after value => Available after.heap value) := by
    rw [body, running_machine]
    exact available
  have framed := SourceRecursiveIntersectionInstructionCredit.bind (compileNode request)
    (fun value => .finishNode 0 value (.pure value)) running.machine 0 1
    (by rw [running_machine]; exact valid) _ _ bodyCredit (by
      intro value after _ _ present
      exact ⟨0, Nat.le_refl _, present⟩)
  have positive := requiredFuel_positive (view heap holds) (SourceRecursiveIntersectionNative.nodeSemantic request) semantic_complete
  have enough := SourceRecursiveIntersectionInstructionProfile.budget_ge_four limit _ positive
  refine ⟨constructed, charged, requestCredit, by cbv, framed, by cbv, by cbv, ?_⟩
  exact Nat.le_trans (by decide : 1 + 1 ≤ 4) enough

/-- Two immutable source occurrences derive ordered call credit and one constructor suffix before any returned list exists. -/
theorem constructed_walk_union_credit :
    built = .done original heap ∧
    Credit heap holds limit
      ((SourceRecursiveIntersectionCode.walk (fun _ : Unit => requestNode request.domain request.left request.right) [(), ()]).bind
        (fun values => .work (makeUnion values) .pure)) machine (2 * amount + 1)
      (fun after value => Available after.heap value) := by
  let input := fun (current : Machine Nat Bool) (_ : Unit) => NodeReady current request
  have stable : Stable input := by
    intro before after growth _ known
    exact ⟨known.1.grows _ growth, growth.available _ known.2.1, growth.available _ known.2.2⟩
  have walked := SourceRecursiveIntersectionInstructionCredit.walk
    (fun _ : Unit => requestNode request.domain request.left request.right) [(), ()] amount input
    (fun after value => Available after.heap value) stable available_stable
    (fun _ _ current _ known => request_node request current amount known charged)
    machine valid (fun _ _ => ready)
  have composed := SourceRecursiveIntersectionInstructionCredit.bind _
    (fun values => .work (makeUnion values) .pure) machine (2 * amount) 1 valid _
    (fun after value => Available after.heap value) walked (by
      intro values after afterValid _ outputs
      exact SourceRecursiveIntersectionInstructionCredit.union values after afterValid outputs.2)
  exact ⟨constructed, composed⟩

#print axioms actual_owner_credit
#check @actual_owner_credit
#print axioms constructed_walk_union_credit
#check @constructed_walk_union_credit
end MicroCFTA.CreditReviewKernels
