import MicroCFTA.SourceCurrentAllocatedNativeInstructionStep
import MicroCFTA.SourceCurrentAllocatedNativePhysicalTraceCompletion

/-!
# Initial semantic credit bounds every physical query prefix

Each yielded step consumes credit. The proof follows the same physical trace
and retains original source records and issued history. A complete trace is
not used to choose its initial budget.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeInstructionTrace
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView IntersectSchedule SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativeFieldClosure (Fields OutcomeFields)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativeInstructionStep (ControlAt)
open SourceRecursiveIntersectionInstructionProfile (budget sourceBranching)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width fuel amount : Nat} {A : Type}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Initial source data determine a mathematical node instruction budget. -/
noncomputable def nodeBudget (source : InternedConstructorTemplates.State Symbol Guard)
    (holds : Guard → Language.Term Symbol → Bool) (request : NodeRequest Symbol Guard) : Nat := by
  classical
  exact if complete : Completes (view source holds) (SourceRecursiveIntersectionNative.nodeSemantic request) then
    budget (sourceBranching source)
      (requiredFuel (view source holds) (SourceRecursiveIntersectionNative.nodeSemantic request) complete)
    else 0

/-- Initial source data determine a mathematical edge instruction budget. -/
noncomputable def edgeBudget (source : InternedConstructorTemplates.State Symbol Guard)
    (holds : Guard → Language.Term Symbol → Bool) (request : EdgeRequest Symbol Guard) : Nat := by
  classical
  exact if complete : Completes (view source holds) (SourceRecursiveIntersectionNative.edgeSemantic holds request) then
    budget (sourceBranching source)
      (requiredFuel (view source holds) (SourceRecursiveIntersectionNative.edgeSemantic holds request) complete)
    else 0

/-- Independent semantic completeness identifies the initial node budget. -/
theorem nodeBudget_of_complete (source : InternedConstructorTemplates.State Symbol Guard)
    (holds : Guard → Language.Term Symbol → Bool) (request : NodeRequest Symbol Guard)
    (complete : Completes (view source holds) (SourceRecursiveIntersectionNative.nodeSemantic request)) :
    nodeBudget source holds request = budget (sourceBranching source)
      (requiredFuel (view source holds) (SourceRecursiveIntersectionNative.nodeSemantic request) complete) := by
  classical
  simp only [nodeBudget, dif_pos complete]

/-- Independent semantic completeness identifies the initial edge budget. -/
theorem edgeBudget_of_complete (source : InternedConstructorTemplates.State Symbol Guard)
    (holds : Guard → Language.Term Symbol → Bool) (request : EdgeRequest Symbol Guard)
    (complete : Completes (view source holds) (SourceRecursiveIntersectionNative.edgeSemantic holds request)) :
    edgeBudget source holds request = budget (sourceBranching source)
      (requiredFuel (view source holds) (SourceRecursiveIntersectionNative.edgeSemantic holds request) complete) := by
  classical
  simp only [edgeBudget, dif_pos complete]

/-- Every actual physical prefix spends at most its original credit. -/
theorem prefix (source : InternedConstructorTemplates.State Symbol Guard) (facts : InternedNestedFacts.Facts source)
    (holds : Guard → Language.Term Symbol → Bool) {control next : Control A} {before after : Checked width}
    (actual : Trace fuel control before next after) (good : Good before) (fields : Fields control before)
    (sourceGrowth : Grows source before.native.machine.heap)
    (sourceHistory : Extends source.nodes.issued before.native.machine.heap.nodes.issued)
    (certificate : ControlAt source holds control before amount post) :
    ∃ remaining, fuel + remaining ≤ amount ∧ ControlAt source holds next after remaining post := by
  induction actual generalizing amount with
  | refl => exact ⟨amount, by omega, certificate⟩
  | cons control before middle current next after count physical one rest ih =>
      obtain ⟨remaining, spent, retained⟩ := SourceCurrentAllocatedNativeInstructionStep.yielded source facts holds
        control middle before current amount post good physical fields sourceGrowth sourceHistory certificate one
      have effects := SourceCurrentAllocatedNativePhysicalCompletion.step_invariants control before good physical fields
      have reached : Good current := by simpa only [one, Outcome.state] using effects.1
      have later : Extension before.native.machine current.native.machine := by
        simpa only [one, Outcome.state] using effects.2.1
      have remainingFields : Fields middle current := by
        simpa only [one, OutcomeFields] using effects.2.2.2.2.2
      obtain ⟨last, tailSpent, final⟩ := ih reached remainingFields
        (grows_trans sourceGrowth later.heap) (extends_trans sourceHistory later.history) retained
      exact ⟨last, by omega, final⟩

/-- A ready original node request bounds every physical prefix from its initial semantic source. -/
theorem node_prefix (source : InternedConstructorTemplates.State Symbol Guard) (facts : InternedNestedFacts.Facts source)
    (holds : Guard → Language.Term Symbol → Bool) (request : NodeRequest Symbol Guard) (scope : NodeScope source request)
    (complete : Completes (view source holds) (SourceRecursiveIntersectionNative.nodeSemantic request))
    {next : Control (Value Symbol Guard)} {before after : Checked width}
    (actual : Trace fuel (.code (requestNode request.domain request.left request.right)) before next after)
    (good : Good before) (ready : NodeReady before.native.machine request)
    (sourceGrowth : Grows source before.native.machine.heap)
    (sourceHistory : Extends source.nodes.issued before.native.machine.heap.nodes.issued) :
    fuel ≤ nodeBudget source holds request := by
  have charged : SourceRecursiveIntersectionInstructionCredit.NodeCharge source holds (sourceBranching source)
      request (nodeBudget source holds request) := by
    refine ⟨scope, complete, ?_⟩
    rw [nodeBudget_of_complete source holds request complete]
  have initial := SourceRecursiveIntersectionInstructionCredit.request_node request before.native.machine _ ready charged
  obtain ⟨remaining, spent, _⟩ := prefix source facts holds actual good (fun _ => trivial)
    sourceGrowth sourceHistory initial
  omega

/-- A ready original edge request bounds every physical prefix from its initial semantic source. -/
theorem edge_prefix (source : InternedConstructorTemplates.State Symbol Guard) (facts : InternedNestedFacts.Facts source)
    (holds : Guard → Language.Term Symbol → Bool) (request : EdgeRequest Symbol Guard) (scope : EdgeScope source request)
    (complete : Completes (view source holds) (SourceRecursiveIntersectionNative.edgeSemantic holds request))
    {next : Control (EdgeValue Symbol Guard)} {before after : Checked width}
    (actual : Trace fuel (.code (requestEdge request.domain request.left request.right)) before next after)
    (good : Good before) (ready : EdgeReady before.native.machine request)
    (sourceGrowth : Grows source before.native.machine.heap)
    (sourceHistory : Extends source.nodes.issued before.native.machine.heap.nodes.issued) :
    fuel ≤ edgeBudget source holds request := by
  have charged : SourceRecursiveIntersectionInstructionCredit.EdgeCharge source holds (sourceBranching source)
      request (edgeBudget source holds request) := by
    refine ⟨scope, complete, ?_⟩
    rw [edgeBudget_of_complete source holds request complete]
  have initial := SourceRecursiveIntersectionInstructionCredit.request_edge request before.native.machine _ ready charged
  obtain ⟨remaining, spent, _⟩ := prefix source facts holds actual good (fun _ => trivial)
    sourceGrowth sourceHistory initial
  omega

end MicroCFTA.SourceCurrentAllocatedNativeInstructionTrace
