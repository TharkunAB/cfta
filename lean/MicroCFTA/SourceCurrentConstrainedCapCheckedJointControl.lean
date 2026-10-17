import MicroCFTA.SourceCurrentConstrainedCapCheckedJointCode
import MicroCFTA.SourceCurrentConstrainedCapNativeGuardHeap
import MicroCFTA.SourceCurrentAllocatedRecursivePrefixReceipt

/-!
# Joint code laws at checked controls

A demanded edge retains a certificate for its actual checked body.
The continuation consumes the same result law as a native memo return.
A yielded instruction produces its joint context from actual past effects.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapCheckedJointControl
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentConstrainedCapKernelJoint (Context)
open SourceCurrentConstrainedCapCheckedJointCode (NodeLaw EdgeLaw)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedRecursivePrefixState (Current)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "CodeCertified" => SourceCurrentConstrainedCapCheckedJointCode.Certified
variable (annotation : Guard → Prop) (source : InternedConstructorTemplates.State Symbol Guard)
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- The original demanded rows supply their exact emitted body law for every actual equality state. -/
def BodyCertified (request : EdgeRequest Symbol Guard) (state : Machine Symbol Guard) : Prop :=
  ∀ width (before after : Checked width) (code : Code Symbol Guard (EdgeValue Symbol Guard)),
    before.native.machine = state → Good before → Context annotation source state → EdgeReady state request →
    body request .pure before = .yielded (.code code) after →
    CodeCertified annotation source code after.native.machine (fun _ value => EdgeLaw annotation source request value)

/-- Checked control certification retains the emitted body and its exact caller continuation. -/
def Certified (control : Control A) (state : Machine Symbol Guard) (post : Machine Symbol Guard → A → Prop) : Prop :=
  match control with
  | .code code => CodeCertified annotation source code state post
  | .edgeBody request next => BodyCertified annotation source request state ∧
      ∀ value after, Extension state after → Context annotation source after → EdgeResident after.heap value →
        EdgeLaw annotation source request value → CodeCertified annotation source (next value) after post

/-- A pure checked control supplies its local result at the identical machine. -/
theorem pure_result (value : A) (state : Machine Symbol Guard) (post : Machine Symbol Guard → A → Prop)
    (certificate : Certified annotation source (.code (.pure value)) state post) : post state value := certificate

/-- Checked sequencing retains the same body certificate and composes its actual effects. -/
theorem certified_bind (control : Control A) (next : A → Code Symbol Guard B)
    (state : Machine Symbol Guard) (context : Context annotation source state)
    (intermediate : Machine Symbol Guard → A → Prop) (post : Machine Symbol Guard → B → Prop)
    (certificate : Certified annotation source control state intermediate)
    (continuation : ∀ value after, Extension state after → Context annotation source after →
      intermediate after value → Certified annotation source (.code (next value)) after post) :
    Certified annotation source (control.bind next) state post := by
  cases control with
  | code code =>
      exact SourceCurrentConstrainedCapCheckedJointCode.certified_bind annotation source code next state context
        intermediate post certificate continuation
  | edgeBody request resume =>
      refine ⟨certificate.1, ?_⟩
      intro value after growth afterContext resident law
      exact SourceCurrentConstrainedCapCheckedJointCode.certified_bind annotation source (resume value) next after afterContext
        intermediate post (certificate.2 value after growth afterContext resident law)
        (fun result final later finalContext middle => continuation result final (growth.trans later) finalContext middle)

/-- Actual physical checks also supply the heap checks for guard retention. -/
theorem physical_inputs (control : Control A) (state : Checked width)
    (inputs : SourceCurrentAllocatedNativePhysicalExecution.Inputs control state) :
    SourceEqualityNativeDemandHeap.Inputs control state := by
  cases control with
  | edgeBody => trivial
  | code code => cases code <;> first | exact inputs | trivial

/-- A yielded step derives the next joint context from current physical and causal facts. -/
theorem yielded_context [DecidableEq Symbol]
    {inventory : List IntersectionFlatMemoKeyDomain.DomainKey}
    {initialDomains : Cache.State IntersectionFlatMemoKeyDomain.DomainKey} (control next : Control A) (before after : Checked width)
    (context : Context annotation source before.native.machine)
    (current : Current source inventory initialDomains after)
    (inputs : SourceCurrentAllocatedNativePhysicalExecution.Inputs control before)
    (one : step control before = .yielded next after) : Context annotation source after.native.machine := by
  have kept := SourceCurrentConstrainedCapNativeGuardHeap.step_heap annotation control before context.semantic
    (physical_inputs control before inputs) context.guards
  have guards : SourceCurrentConstrainedCapGuardHeap.Heap annotation after.native.machine.heap := by
    simpa only [one, Outcome.state] using kept
  exact ⟨current.good.native.machine, current.semantic.ready.semantic, guards, current.growth, current.history⟩

end MicroCFTA.SourceCurrentConstrainedCapCheckedJointControl
