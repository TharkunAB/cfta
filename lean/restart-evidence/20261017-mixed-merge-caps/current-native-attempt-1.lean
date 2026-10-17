import MicroCFTA.SourceCurrentConstrainedCapCheckedJointInventoryCold
import MicroCFTA.SourceCurrentAllocatedTargetQuery

/-!
# Joint native laws at the literal current heap

Each completed prefix rebases its captured laws to its actual returned heap.
The native cells retain their original request witnesses. A supplied checked
query trace derives the next cap and all new origins before that rebase.
This component verifies actual returns. It does not assert query completion.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapCurrentNative
open Cache Language IntersectSchedule InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView SourceEqualityNativeDemand
open SourceCurrentConstrainedCapKernelJoint (Context)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceEqualityRequiredSemanticCache (SemanticReady)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Joint" => SourceCurrentConstrainedCapCheckedJointCache.Stored
local notation "Origins" => SourceCurrentConstrainedCapCheckedJointOrigins.Stored
variable {width : Nat}

/-- The current physical heap interprets both joint memo laws and all captured request origins. -/
def At (annotation : Guard → Prop) (state : Checked width) : Prop :=
  Context annotation state.native.machine.heap state.native.machine ∧
    Joint annotation state.native.machine.heap state.native ∧ Origins state.native.machine.heap state.native

/-- Actual source growth rebases both stored families at the same complete checked state. -/
theorem rebase (annotation : Guard → Prop) (source : InternedConstructorTemplates.State Symbol Guard)
    (state : Checked width) (facts : Facts source) (good : Good state)
    (context : Context annotation source state.native.machine)
    (stored : Joint annotation source state.native) (origins : Origins source state.native) : At annotation state := by
  have rebased := SourceCurrentConstrainedCapCheckedJointRebase.rebase annotation source state.native facts
    context.growth context.history good.native origins stored
  exact ⟨⟨good.native.machine, context.semantic, context.guards, grows_refl _, extends_refl _⟩, rebased⟩

/-- Literal unchanged cells retain their laws through a proved physical and guard-heap extension. -/
theorem advance (annotation : Guard → Prop) (before after : Checked width)
    (current : At annotation before) (good : Good after)
    (semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap after.native.machine.heap)
    (guards : SourceCurrentConstrainedCapGuardHeap.Heap annotation after.native.machine.heap)
    (extension : Extension before.native.machine after.native.machine)
    (nodes : after.native.nodes = before.native.nodes) (edges : after.native.edges = before.native.edges) :
    At annotation after := by
  have stored : Joint annotation before.native.machine.heap after.native :=
    ⟨by simpa only [nodes] using current.2.1.nodes, by simpa only [edges] using current.2.1.edges⟩
  have origins : Origins before.native.machine.heap after.native :=
    ⟨by simpa only [nodes] using current.2.2.nodes, by simpa only [edges] using current.2.2.edges⟩
  exact rebase annotation before.native.machine.heap after current.1.valid.1 good
    (current.1.after good.native.machine semantic guards extension) stored origins

/-- The same actual checked query derives its cap, closed syntax, and next current-heap stores. -/
theorem step [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) (depth : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {left right result : Value Symbol Guard} {before after : Checked width}
    (actual : SourceCurrentAllocatedTargetQuery.Step left right before result after)
    (good : Good before) (semantic : SemanticReady before.native.machine.heap) (current : At annotation before)
    (leftAvailable : Available before.native.machine.heap left) (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (leftCap : SourceCurrentConstrainedCap.Cap annotation depth left)
    (rightCap : SourceCurrentConstrainedCap.Cap annotation depth right) :
    At annotation after ∧ SourceCurrentConstrainedCap.Cap annotation depth result ∧ result.free = [] ∧
      Original result ∧ SourceCurrentConstrainedCapNativeProbeSupport.ProbeFree result := by
  cases actual with
  | run trace =>
      let source := before.native.machine.heap
      let holds := SourceEqualityPCSGuard.holds formulas solver
      let domains := SourceRecursiveIntersectionSourceInventory.domains source
      let request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩
      have facts := good.native.machine.1
      have leftOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original left source facts.coherent leftAvailable leftClosed
      have rightOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original right source facts.coherent rightAvailable rightClosed
      let inventory := SourceCurrentAllocatedNativeInventoryCold.pairInventory source facts left right
        leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed
      let inputs := inventory.inputs holds
      have reached := SourceCurrentAllocatedRecursivePrefixState.initial source domains before good semantic rfl
      have scope := initial_scope source left right leftOriginal rightOriginal leftAvailable rightAvailable
      have ready : NodeReady before.native.machine request := ⟨empty_domain _, leftAvailable, rightAvailable⟩
      have physical := SourceCurrentAllocatedRecursivePrefixCode.request_node source domains request before.native.machine
        ready scope (SourceRecursiveIntersectionSourceInventory.empty_mem source)
      have certificate : SourceCurrentConstrainedCapCheckedJointControl.Certified annotation source
          (.code (requestNode request.domain left right)) before.native.machine
          (fun _ value => SourceCurrentConstrainedCapCheckedJointCode.NodeLaw annotation source request value) :=
        fun _ _ _ _ _ law => law
      have joint := SourceCurrentConstrainedCapCheckedJointTrace.completed facts
        (SourceCurrentAllocatedRecursiveDomainCode.source_closed source facts) _
        (.code (requestNode request.domain left right)) before _ result _ _ reached physical (fun _ => trivial)
        current.1 certificate current.2.1 trace
      have originalInputs : ∀ input, inputs.valid input → OriginalInput source input :=
        SourceCurrentAllocatedNativeInputInventoryModels.reachable_original source facts holds inventory.roots
          inventory.originals inventory.available inventory.closed
      have leftValid := SourceCurrentAllocatedNativeInputInventoryModels.root_valid source facts holds inventory.roots
        inventory.originals inventory.available inventory.closed left
        (by simp [inventory, SourceCurrentAllocatedNativeInventoryCold.pairInventory])
      have rightValid := SourceCurrentAllocatedNativeInputInventoryModels.root_valid source facts holds inventory.roots
        inventory.originals inventory.available inventory.closed right
        (by simp [inventory, SourceCurrentAllocatedNativeInventoryCold.pairInventory])
      have known : SourceCurrentAllocatedNativeAdmissionCache.NodeCovered inputs request :=
        ⟨⟨leftOriginal, rightOriginal, leftValid, rightValid⟩, SourceCurrentAllocatedNativePairAdmission.empty_seen inputs⟩
      have localCertificate := SourceCurrentAllocatedNativeAdmissionCode.requestNode_certified source holds inputs request
        before.native.machine scope known
      have captured := SourceCurrentConstrainedCapCheckedJointOriginTrace.Trace.origins source holds inputs facts
        originalInputs trace (fun final value => Available final.heap value) good semantic
        (grows_refl _) (extends_refl _) (fun _ => trivial) current.2.2 localCertificate
      have supported := SourceCurrentConstrainedCapOriginalSupport.closed_inputs source facts request.domain left right
        leftAvailable rightAvailable leftClosed rightClosed
      have law := joint.result depth (SourceCurrentConstrainedCapOriginalSupport.empty annotation source)
        supported leftCap rightCap
      have closed := SourceRecursiveIntersectionResultScope.empty_scope result law.2.2
      have original := SourceRecursiveIntersectionOriginalOutput.closed_original result _ joint.context.valid.1.coherent
        joint.physical closed
      exact ⟨rebase annotation source _ facts joint.current.good joint.context joint.stored captured.1,
        law.1, closed, original, SourceCurrentConstrainedCapNativeProbeSupport.of_closed result closed⟩

end MicroCFTA.SourceCurrentConstrainedCapCurrentNative
