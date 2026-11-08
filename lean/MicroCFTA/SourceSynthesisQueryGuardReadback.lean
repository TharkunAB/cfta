import MicroCFTA.SourceSynthesisNativeGuardOrigins
import MicroCFTA.SourceCurrentNativeOpenQueryRowOrigins

/-!
# Original guard provenance at actual checked query rows

The original accepted construction supplies the guard alphabet. Actual
checked traces retain conjunction origins at physical returned rows.
The readback includes the existing self, join, Mu, union, and reference
writer cases. Stored winners retain their captured writer.

The warm prefix has its actual initial code checks and physical Good.
No final annotation heap or final publication history is an input.
The result does not restrict guards to Type sites or prove a decreasing
rank, a finite conjunction closure, or complete enumeration.
-/
namespace MicroCFTA.SourceSynthesisQueryGuardReadback
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand (Control)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression firstOrderRaw)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisNativeGuardOrigins (Origin)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentNativeEdgeWriterGrowth (History)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "CtorState" => InternedConstructorTemplates.State Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
local notation "Publications" => SourceCurrentNativeMuPublication.History
local notation "Resolved" => SourceCurrentNativeOpenQueryRowOrigins.Resolved
variable {width fuel : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem physical_readback (lib : Library)
    {before after : Checked width} (input : NodeRequest Symbol Guard)
    (result : Node) (good : Good before) (history : History before)
    (publications : Publications empty before.native.machine.heap)
    (actual : Trace fuel (.code (requestNode input.domain input.left input.right))
      before (.code (.pure result)) after)
    (known : SourceEqualityAnnotationHeap.Heap (Origin lib) after.native.machine.heap)
    (index : Nat) (row : EdgeValue Symbol Guard)
    (selected : (nodeEdges result)[index]? = some row) :
    Good after ∧ EdgeResident after.native.machine.heap row ∧
      Origin lib row.entry.key.constraint ∧ Resolved after input result index row := by
  obtain ⟨_, checked, _, _, resolved⟩ := SourceCurrentNativeOpenQueryRowOrigins.request
    input fuel result good history publications actual index row selected
  have available : Available after.native.machine.heap result := by
    obtain ⟨terminal, handle, _, _, _, returned, _, _⟩ := resolved
    exact (checked.native.nodes.checked handle _ returned).2
  have resident := resident_edges after.native.machine.heap checked.native.machine.1.linked result
    available.resident row (List.mem_of_getElem? selected)
  exact ⟨checked, resident, known row.entry.key row resident, resolved⟩

/-- An actual query connects its full captured row origin to the original source guard alphabet. -/
theorem request_readback (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (accepted : firstOrderRaw lib query signed = .ok expression)
    (value : Node) (heap : CtorState)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols expression) [] empty = .done value heap)
    {before after : Checked width} (input : NodeRequest Symbol Guard) (result : Node)
    (initialHeap : before.native.machine.heap = heap) (good : Good before)
    (history : History before) (publications : Publications empty before.native.machine.heap)
    (actual : Trace fuel (.code (requestNode input.domain input.left input.right))
      before (.code (.pure result)) after)
    (index : Nat) (row : EdgeValue Symbol Guard)
    (selected : (nodeEdges result)[index]? = some row) :
    Good after ∧ EdgeResident after.native.machine.heap row ∧
      Origin lib row.entry.key.constraint ∧ Resolved after input result index row := by
  exact physical_readback lib input result good history publications actual
    (SourceSynthesisNativeGuardOrigins.request_heap lib query signed expression accepted value heap built
      initialHeap actual good) index row selected

/-- The actual original build and empty native memos derive both causal histories. -/
theorem cold_request_readback (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (accepted : firstOrderRaw lib query signed = .ok expression)
    (value : Node) (heap : CtorState)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols expression) [] empty = .done value heap)
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (after : Checked width) (input : NodeRequest Symbol Guard) (result : Node)
    (good : Good (⟨initial width ⟨heap, Cache.emptyState⟩, operations⟩ : Checked width))
    (actual : Trace fuel (.code (requestNode input.domain input.left input.right))
      (⟨initial width ⟨heap, Cache.emptyState⟩, operations⟩ : Checked width) (.code (.pure result)) after)
    (index : Nat) (row : EdgeValue Symbol Guard)
    (selected : (nodeEdges result)[index]? = some row) :
    Good after ∧ EdgeResident after.native.machine.heap row ∧
      Origin lib row.entry.key.constraint ∧ Resolved after input result index row := by
  have publications : Publications empty heap := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using
      SourceCurrentNativeMuPublication.closed_history (ordinarySymbols expression)
  exact request_readback lib query signed expression accepted value heap built input result rfl good
    (.initial ⟨heap, Cache.emptyState⟩ operations) publications actual index row selected

/-- An actual warm prefix derives the later query's row guard without a future heap or history premise. -/
theorem warm_request_readback (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (accepted : firstOrderRaw lib query signed = .ok expression)
    (value : Node) (heap : CtorState)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols expression) [] empty = .done value heap)
    (operations : SourceEqualityConstraintMemoAllocation.State)
    {A : Type} (code : Code Symbol Guard A) (prior : A) (warmFuel : Nat)
    {before after : Checked width} (input : NodeRequest Symbol Guard) (result : Node)
    (good : Good (⟨initial width ⟨heap, Cache.emptyState⟩, operations⟩ : Checked width))
    (clean : BodyCode code)
    (allocated : SourceCurrentAllocatedNativeCodeFields.Fields operations code)
    (fields : SourceCurrentNativeGuardCode.Fields
      (fun guard => guard ∈ SourceSynthesisOriginalGuardAlphabet.alphabet lib) code)
    (warm : Trace warmFuel (.code code)
      (⟨initial width ⟨heap, Cache.emptyState⟩, operations⟩ : Checked width) (.code (.pure prior)) before)
    (actual : Trace fuel (.code (requestNode input.domain input.left input.right))
      before (.code (.pure result)) after)
    (index : Nat) (row : EdgeValue Symbol Guard)
    (selected : (nodeEdges result)[index]? = some row) :
    Good after ∧ EdgeResident after.native.machine.heap row ∧
      Origin lib row.entry.key.constraint ∧ Resolved after input result index row := by
  let cold : Checked width := ⟨initial width ⟨heap, Cache.emptyState⟩, operations⟩
  let next : A → Code Symbol Guard Node := fun _ => requestNode input.domain input.left input.right
  have reached := SourceCurrentAllocatedNativeSemanticTraceReadback.effects warm good allocated
  have history : History before := .trace (.initial ⟨heap, Cache.emptyState⟩ operations)
    (.code code) warmFuel prior clean good allocated warm
  have original : cold.native.machine.heap =
      (InternedFreshOrdinaryConstruction.build (ordinarySymbols expression) [] empty).state := by
    rw [built]
    rfl
  obtain ⟨_, ⟨publications⟩⟩ := SourceCurrentNativePublicationTrace.source_trace
    (ordinarySymbols expression) warm original
  have liftedWarm := warm.bind next
  change Trace warmFuel (.code (code.bind next)) cold
    (.code (requestNode input.domain input.left input.right)) before at liftedWarm
  have combined := liftedWarm.trans actual
  have fullAllocated : SourceCurrentAllocatedNativeCodeFields.Fields operations (code.bind next) :=
    SourceCurrentAllocatedNativeCodeFields.fields_bind operations code next allocated (fun _ _ => trivial)
  have fullFields : SourceCurrentNativeGuardCode.Fields
      (fun guard => guard ∈ SourceSynthesisOriginalGuardAlphabet.alphabet lib) (code.bind next) :=
    SourceCurrentNativeGuardCode.bind _ code next fields (fun _ _ => trivial)
  have known := SourceSynthesisNativeGuardOrigins.trace_heap lib query signed expression accepted value heap built
    (before := cold) rfl combined good fullAllocated fullFields
  exact physical_readback lib input result reached.1 history publications actual known index row selected

end MicroCFTA.SourceSynthesisQueryGuardReadback
