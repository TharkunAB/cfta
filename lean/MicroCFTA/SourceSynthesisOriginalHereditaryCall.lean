import MicroCFTA.SourceSynthesisHereditaryOuterTraversal
import MicroCFTA.SourceSynthesisOriginalHereditaryProgramFields
import MicroCFTA.SourceSynthesisOriginalCallerInitialization
import MicroCFTA.SourceSynthesisOriginalTypeSharedState
import MicroCFTA.SourceCurrentConstrainedCapGuardExecution

/-!
# Recursive fields through an actual original root call

Accepted signed source input derives its allocation preparation, build,
initial caller, recursive Program fields and conditional Type stores.
Closed source construction derives the guard profile for the same heap.
Both outer result families start empty. No initial field, context, profile
or memo certificate is supplied.
The caller is the modeled cold caller. Native CAF initialization requires
a separate correspondence proof.

The result applies to the same successful bounded worker call. Reached
ranges and successful execution remain explicit premises. Source errors
remain outside the accepted branch. This theorem does not prove completion,
failure-prefix preservation or an original-input resource bound.
-/
namespace MicroCFTA.SourceSynthesisOriginalHereditaryCall
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisFirstOrderConstruction (Expression firstOrderRaw)
open SourceSynthesisUniverseCallerBoundary (ordinarySymbols)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceSynthesisHereditaryProgramFields (ValueFields)
open SourceCurrentAllocatedPartialState (NodeRequest)
open SourceCurrentAllocatedPartialWorker (nodeCall)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedPartialInitialization (caller emptyValue checked operations inventory globals)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
local notation "SharedReady" => SourceSynthesisNativeTypeSharedState.Ready
local notation "initialShared" => SourceCurrentAllocatedSharedTargetState.initial
local notation "GuardHeap" => SourceCurrentConstrainedCapGuardHeap.Heap
local notation "History" => SourceSynthesisHereditaryClosedMemo.History
local notation "NodeFields" => SourceSynthesisHereditaryClosedMemo.NodeFields
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- Original source derives every initial certificate for the same successful root call. -/
theorem accepted
    (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (returned : firstOrderRaw lib query signed = .ok expression)
    (width : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∃ fields cache value heap,
      ∃ built : InternedFreshOrdinaryConstruction.build (ordinarySymbols expression) [] empty = .done value heap,
      SourceEqualityOriginalAllocationPreparation.Receipt
        (SourceEqualityConstraintOrigins.guards (ordinarySymbols expression)) Cache.emptyState fields cache ∧
      Context formulas solver (inventory (ordinarySymbols expression) value heap built)
        (caller width cache heap) globals ∧
      Available heap value ∧ value.free = [] ∧ ValueFields (Origin lib) literal value ∧
      ∀ {fuel g s r e p h m c n budget : Nat} {result : Node} {after : Caller width},
        SourceCurrentAllocatedPartialWorkerRanges.nodeCall fuel g s r e p h m c n budget
          (⟨emptyValue cache, value⟩ : NodeRequest) (caller width cache heap) →
        nodeCall fuel g s r e p h m c n budget ⟨emptyValue cache, value⟩ (caller width cache heap) = .done result after →
        ∃ next final, ∃ graph : SourceCurrentAllocatedPartialGraph.NodeCall budget
          ⟨emptyValue cache, value⟩ (caller width cache heap) result after,
          SourceCurrentAllocatedPartialSourceReads.NodeCallReads formulas solver graph globals final ∧
          SourceCurrentAllocatedPartialChecks.Checks (SourceCurrentAllocatedPartialChecks.nodeCallTrace graph) ∧
          Post formulas solver next (caller width cache heap) after final ∧
          Available after.checked.native.machine.heap result ∧
          SourceCurrentAllocatedPartialMemoSound.NodeLaw formulas solver ⟨emptyValue cache, value⟩ result ∧
          SharedReady lib (initialShared after.checked after.merge) ∧
          GuardHeap (Origin lib) after.checked.native.machine.heap ∧ History lib literal after ∧
          result.free = [] ∧ NodeFields lib literal ⟨emptyValue cache, value⟩ result ∧
          ValueFields (Origin lib) literal result := by
  obtain ⟨fields, cache, value, heap, built, prepared, context, _facts, available, _roles,
      _growth, _history, _identity, emptySame, inherited, closed, _original⟩ :=
    SourceSynthesisOriginalCallerInitialization.accepted lib query signed expression returned width
      Cache.emptyState Cache.empty_valid formulas solver
  have sourceFields := SourceSynthesisOriginalHereditaryProgramFields.firstOrderRaw_fields
    lib query signed expression returned value heap built
  have typedState : SharedReady lib
      (initialShared (caller width cache heap).checked (caller width cache heap).merge) :=
    SourceSynthesisOriginalTypeSharedState.initial_ready lib query signed expression returned value heap built width
      (operations cache) context.ready.good
  have profile : GuardHeap (Origin lib) heap := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using
      SourceCurrentConstrainedCapGuardExecution.closed_heap (Origin lib) (ordinarySymbols expression)
  have history : History lib literal (caller width cache heap) :=
    SourceSynthesisHereditaryClosedMemo.initial lib literal (checked width cache heap)
      SourceCurrentMemoMergeGraph.empty SourceCurrentEmptinessMemo.empty
  have inheritedReady : SourceEqualityConstraintAllocation.Ready
      (caller width cache heap).checked.operations.constraints (emptyValue cache) := by
    rw [emptySame]
    exact inherited
  refine ⟨fields, cache, value, heap, built, prepared, context, available, closed, sourceFields, ?_⟩
  intro fuel g s r e p h m c n budget result after ranges done
  obtain ⟨next, final, graph, reads, checks, post, output, law, nextReady, nextProfile,
      nextHistory, resultClosed, resultFields⟩ :=
    SourceSynthesisHereditaryOuterTraversal.nodeCall_fields lib literal formulas solver
      (request := ⟨emptyValue cache, value⟩) context typedState
      profile history inheritedReady available closed (Or.inr sourceFields) ranges done
  exact ⟨next, final, graph, reads, checks, post, output, law, nextReady, nextProfile,
    nextHistory, resultClosed, resultFields, resultFields.program sourceFields⟩

end MicroCFTA.SourceSynthesisOriginalHereditaryCall
