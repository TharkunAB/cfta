import MicroCFTA.SourceCurrentAllocatedNativePhysicalCompletion
import MicroCFTA.SourceCurrentAllocatedNativeSemanticHeap
import MicroCFTA.SourceCurrentAllocatedNativeDomainTrace

/-!
# Current state facts from an executed recursive prefix

The state facts retain the original heap separately from the current domain
cache. One actual admitted instruction extends the past allocation history.
No future execution or completed recursive result occurs in the premises.
-/
namespace MicroCFTA.SourceCurrentAllocatedRecursivePrefixState
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativeFieldClosure (Fields)
open SourceEqualityRequiredSemanticCache (SemanticReady)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocation" => SourceRecursiveIntersectionDomainAllocation.Trace
local notation "Inputs" => SourceCurrentAllocatedNativePhysicalExecution.Inputs
local notation "Entered" => SourceCurrentAllocatedNativeDomainTrace.Entered
variable {A : Type} {width : Nat}

/-- Current facts retain only the original source and already executed allocations. -/
structure Current (source : InternedConstructorTemplates.State Symbol Guard)
    (inventory : List IntersectionFlatMemoKeyDomain.DomainKey)
    (initial : Cache.State IntersectionFlatMemoKeyDomain.DomainKey) (state : Checked width) : Prop where
  /-- Both native memo families and the equality fields are valid. -/
  good : Good state
  /-- The current heap retains its semantic readiness. -/
  semantic : SemanticReady state.native.machine.heap
  /-- The current heap retains every original source record. -/
  growth : Grows source state.native.machine.heap
  /-- The current heap retains every original issued identity. -/
  history : Cache.Extends source.nodes.issued state.native.machine.heap.nodes.issued
  /-- The current domain cache follows the actual past allocations. -/
  domains : Allocation inventory initial state.native.machine.domains

/-- The initial checked state has an empty actual domain allocation history. -/
theorem initial (source : InternedConstructorTemplates.State Symbol Guard)
    (inventory : List IntersectionFlatMemoKeyDomain.DomainKey) (state : Checked width)
    (good : Good state) (semantic : SemanticReady state.native.machine.heap)
    (same : state.native.machine.heap = source) :
    Current source inventory state.native.machine.domains state := by
  refine ⟨good, semantic, ?_, ?_, .refl _⟩
  · rw [same]; exact grows_refl _
  · rw [same]; exact Cache.extends_refl _

/-- An actual yielded instruction retains all current facts and its exact effects. -/
theorem yielded [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {source : InternedConstructorTemplates.State Symbol Guard}
    {inventory : List IntersectionFlatMemoKeyDomain.DomainKey}
    {initial : Cache.State IntersectionFlatMemoKeyDomain.DomainKey}
    (control next : Control A) (before after : Checked width)
    (current : Current source inventory initial before)
    (inputs : Inputs control before) (admitted : Entered inventory control)
    (fields : Fields control before)
    (one : SourceEqualityNativeDemand.step control before = .yielded next after) :
    Current source inventory initial after ∧
      Extension before.native.machine after.native.machine ∧
      SourceEqualityRequiredCache.Keeps before.native.machine.heap after.native.machine.heap ∧
      SourceEqualityConstraintMemoAllocation.Grows before.operations after.operations ∧ Fields next after := by
  have checked := SourceCurrentAllocatedNativePhysicalCompletion.step_invariants control before current.good inputs fields
  have actual : Good after ∧ Extension before.native.machine after.native.machine ∧
      SourceEqualityRequiredCache.Keeps before.native.machine.heap after.native.machine.heap ∧
      SourceEqualityConstraintMemoAllocation.Grows before.operations after.operations ∧
      SourceCurrentAllocatedNativeFieldClosure.OutcomeFields (.yielded next after) := by
    simpa only [one, Outcome.state] using checked
  have semantic := SourceCurrentAllocatedNativeSemanticHeap.step_semantic control before current.semantic
    (SourceCurrentAllocatedNativePhysicalExecution.inputs_heap control before inputs)
  have keptSemantic : SemanticReady after.native.machine.heap := by
    simpa only [one, Outcome.state] using semantic
  have domains := SourceCurrentAllocatedNativeDomainTrace.yielded inventory control next before after admitted one
  exact ⟨⟨actual.1, keptSemantic, grows_trans current.growth actual.2.1.heap,
    Cache.extends_trans current.history actual.2.1.history, current.domains.trans domains⟩,
    actual.2.1, actual.2.2.1, actual.2.2.2.1, actual.2.2.2.2.2⟩

end MicroCFTA.SourceCurrentAllocatedRecursivePrefixState
