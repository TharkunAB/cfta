import MicroCFTA.SourceCurrentHereditaryNativePhysicalTrace
import MicroCFTA.SourceCurrentAllocatedTargetQuery
import MicroCFTA.SourceRecursiveIntersectionOriginalOutput

/-!
# Hereditary laws for the same actual warm target query

The supplied query carries each executed physical input check. Local source
scope is computed at its entry heap. Empty-table initialization and actual
finishes establish the universal causal store. No future range or capacity
condition is required by this preservation theorem.
-/
namespace MicroCFTA.SourceCurrentHereditaryTargetQuery
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand SourceEqualityAnnotationLanguage
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceEqualityRequiredSemanticCache (SemanticReady)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "Stored" => SourceCurrentHereditaryNativeUniversalStore.Stored Plain
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
variable {width : Nat} {left right result : Value Symbol Guard} {before after : Checked width}

/-- An admitted actual warm query retains causal stores and derives its own hereditary result. -/
theorem step (actual : SourceCurrentAllocatedTargetQuery.Step left right before result after)
    (good : Good before) (semantic : SemanticReady before.native.machine.heap)
    (leftAvailable : Available before.native.machine.heap left)
    (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (stored : Stored before) (leftAnnotated : Annotated Plain left) (rightAnnotated : Annotated Plain right) :
    Stored after ∧ Annotated Plain result := by
  cases actual with
  | run trace =>
    let source := before.native.machine.heap
    let inventory := SourceRecursiveIntersectionSourceInventory.domains source
    let request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩
    have facts : InternedNestedFacts.Facts source := good.native.machine.1
    have leftOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original left source facts.coherent leftAvailable leftClosed
    have rightOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original right source facts.coherent rightAvailable rightClosed
    have scope := initial_scope source left right leftOriginal rightOriginal leftAvailable rightAvailable
    have current : SourceCurrentAllocatedRecursivePrefixState.Current source inventory before.native.machine.domains before :=
      SourceCurrentAllocatedRecursivePrefixState.initial source inventory before good semantic rfl
    have physical : SourceCurrentAllocatedRecursivePrefixControl.Certified source inventory
        (.code (requestNode request.domain left right)) before.native.machine
        (fun final value => Available final.heap value) :=
      SourceCurrentAllocatedRecursivePrefixCode.request_node source inventory request before.native.machine
        ⟨empty_domain _, leftAvailable, rightAvailable⟩ scope (SourceRecursiveIntersectionSourceInventory.empty_mem source)
    have certificate : SourceCurrentHereditaryNativeControl.Certified Plain source
        (.code (requestNode request.domain left right)) before.native.machine
        (fun final value => Available final.heap value ∧ Annotated Plain value) :=
      SourceCurrentHereditaryNativeEffects.request_node Plain source request before.native.machine
        (SourceCurrentHereditaryNativeScope.empty Plain source) leftAnnotated rightAnnotated
    have retained := SourceCurrentHereditaryNativePhysicalTrace.completed facts
      (SourceCurrentAllocatedRecursiveDomainCode.source_closed source facts) _ _ before after result _ _
      current physical (fun _ => trivial) certificate stored trace
    exact ⟨retained.stored, retained.result.2⟩

/-- The existing full query receipt and its complete returned state stay unchanged. -/
theorem receipt
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : SourceCurrentAllocatedNativeInventoryState.Inventory) (memos : EndpointMemoGateTrace.Memos)
    (actual : SourceCurrentAllocatedTargetQuery.Receipt formulas solver inventory left right before result after memos)
    (ready : SourceCurrentConjunctionClassScan.Ready before)
    (leftAvailable : Available before.native.machine.heap left) (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (stored : Stored before) (leftAnnotated : Annotated Plain left) (rightAnnotated : Annotated Plain right) :
    SourceCurrentAllocatedTargetQuery.Receipt formulas solver inventory left right before result after memos ∧
      Stored after ∧ Annotated Plain result :=
  ⟨actual, step actual.actual ready.good ready.semantic leftAvailable rightAvailable leftClosed rightClosed stored leftAnnotated rightAnnotated⟩

end MicroCFTA.SourceCurrentHereditaryTargetQuery
