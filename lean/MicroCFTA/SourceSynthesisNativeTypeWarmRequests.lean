import MicroCFTA.SourceSynthesisNativeTypeTrace

/-!
# Consecutive actual checked Type queries

The first actual query derives the warm stores, physical Good, and semantic
heap. The second query uses that same state and both native memo tables.
Its computed source is the actual warm heap. Its initial domain cache is
the actual warm cache, which can be nonempty.

Only the next query's available closed Type operands remain local inputs.
There is no supplied future return, store, context, or code certificate.
Both root requests use the literal empty domain. An open-domain request
also needs Type ancestry for its bound names. These laws do not derive
that ancestry, trace existence, or a global resource bound.
-/
namespace MicroCFTA.SourceSynthesisNativeTypeWarmRequests
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisFirstOrderConstruction
open SourceSynthesisNativeTypeTrace (Origin cold origin_top origin_conjoin)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Good" => SourceCurrentAllocatedNativePhysicalCompletion.Good
local notation "SemanticReady" => SourceEqualityRequiredSemanticCache.SemanticReady
local notation "Stored" => SourceCurrentHereditaryNativeUniversalStore.Stored
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem continue_request {width : Nat} (lib : Library) (before : Checked width)
    (good : Good before) (semantic : SemanticReady before.native.machine.heap)
    (stored : Stored (Origin lib) before)
    (left right : Value Symbol Guard)
    (leftAvailable : Available before.native.machine.heap left)
    (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (leftTyped : Annotated (Origin lib) left) (rightTyped : Annotated (Origin lib) right)
    (fuel : Nat) (result : Value Symbol Guard) (after : Checked width)
    (actual : Trace fuel (.code (requestNode IntersectionEmptyDomain.emptyDomain left right))
      before (.code (.pure result)) after) :
    SourceCurrentHereditaryNativeGeneralInduction.Return (Origin lib)
      (source := before.native.machine.heap)
      (inventory := SourceRecursiveIntersectionSourceInventory.domains before.native.machine.heap)
      (initial := before.native.machine.domains) before after result
      (fun final output => Available final.heap output)
      (fun final output => Available final.heap output ∧ Annotated (Origin lib) output) := by
  let source := before.native.machine.heap
  let inventory := SourceRecursiveIntersectionSourceInventory.domains source
  let request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩
  have facts := good.native.machine.1
  have current : SourceCurrentAllocatedRecursivePrefixState.Current source inventory
      before.native.machine.domains before :=
    SourceCurrentAllocatedRecursivePrefixState.initial source inventory before good semantic rfl
  have scope := initial_scope source left right
    (SourceRecursiveIntersectionOriginalOutput.closed_original left source facts.coherent leftAvailable leftClosed)
    (SourceRecursiveIntersectionOriginalOutput.closed_original right source facts.coherent rightAvailable rightClosed)
    leftAvailable rightAvailable
  have physical : SourceCurrentAllocatedRecursivePrefixControl.Certified source inventory
      (.code (requestNode request.domain request.left request.right)) before.native.machine
      (fun final output => Available final.heap output) :=
    SourceCurrentAllocatedRecursivePrefixCode.request_node source inventory request before.native.machine
      ⟨SourceRecursiveIntersectionKernel.empty_domain before.native.machine, leftAvailable, rightAvailable⟩ scope
      (SourceRecursiveIntersectionSourceInventory.empty_mem source)
  have certificate : SourceCurrentHereditaryNativeControl.Certified (Origin lib) source
      (.code (requestNode request.domain request.left request.right)) before.native.machine
      (fun final output => Available final.heap output ∧ Annotated (Origin lib) output) :=
    SourceCurrentHereditaryNativeEffects.request_node (Origin lib) source request before.native.machine
      (SourceCurrentHereditaryNativeScope.empty (Origin lib) source) leftTyped rightTyped
  have preserves := SourceCurrentHereditaryNativeGeneralPhysicalTrace.completed
    (source := source) (inventory := inventory) (initial := before.native.machine.domains) (width := width)
    (A := Value Symbol Guard) (Origin lib) (origin_top lib) (origin_conjoin lib) facts
    (SourceCurrentAllocatedRecursiveDomainCode.source_closed source facts) fuel
  exact preserves (.code (requestNode request.domain request.left request.right)) before after result _ _
    current physical (fun _ => trivial) certificate stored actual

/-- Two actual queries retain Type origins across the changed warm heap and both native memo families. -/
theorem two_requests
    (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (accepted : firstOrderRaw lib query signed = .ok expression)
    (value : Value Symbol Guard) (heap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build
      (SourceSynthesisUniverseCallerBoundary.ordinarySymbols expression) [] empty = .done value heap)
    (width : Nat) (operations : SourceEqualityConstraintMemoAllocation.State)
    (good : Good (cold width heap operations))
    (firstLeft firstRight : Value Symbol Guard)
    (firstLeftAvailable : Available heap firstLeft) (firstRightAvailable : Available heap firstRight)
    (firstLeftClosed : firstLeft.free = []) (firstRightClosed : firstRight.free = [])
    (firstLeftTyped : Annotated (Origin lib) firstLeft) (firstRightTyped : Annotated (Origin lib) firstRight)
    (firstFuel : Nat) (firstResult : Value Symbol Guard) (middle : Checked width)
    (firstActual : Trace firstFuel (.code (requestNode IntersectionEmptyDomain.emptyDomain firstLeft firstRight))
      (cold width heap operations) (.code (.pure firstResult)) middle)
    (nextLeft nextRight : Value Symbol Guard)
    (nextLeftAvailable : Available middle.native.machine.heap nextLeft)
    (nextRightAvailable : Available middle.native.machine.heap nextRight)
    (nextLeftClosed : nextLeft.free = []) (nextRightClosed : nextRight.free = [])
    (nextLeftTyped : Annotated (Origin lib) nextLeft) (nextRightTyped : Annotated (Origin lib) nextRight)
    (nextFuel : Nat) (nextResult : Value Symbol Guard) (after : Checked width)
    (nextActual : Trace nextFuel (.code (requestNode IntersectionEmptyDomain.emptyDomain nextLeft nextRight))
      middle (.code (.pure nextResult)) after) :
    SourceCurrentHereditaryNativeGeneralInduction.Return (Origin lib)
      (source := heap) (inventory := SourceRecursiveIntersectionSourceInventory.domains heap)
      (initial := Cache.emptyState) (cold width heap operations) middle firstResult
      (fun final output => Available final.heap output)
      (fun final output => Available final.heap output ∧ Annotated (Origin lib) output) ∧
    SourceCurrentHereditaryNativeGeneralInduction.Return (Origin lib)
      (source := middle.native.machine.heap)
      (inventory := SourceRecursiveIntersectionSourceInventory.domains middle.native.machine.heap)
      (initial := middle.native.machine.domains) middle after nextResult
      (fun final output => Available final.heap output)
      (fun final output => Available final.heap output ∧ Annotated (Origin lib) output) := by
  have first := SourceSynthesisNativeTypeTrace.request_completed lib query signed expression accepted value heap built
    width operations good firstLeft firstRight firstLeftAvailable firstRightAvailable firstLeftClosed firstRightClosed
    firstLeftTyped firstRightTyped firstFuel firstResult middle firstActual
  have next := continue_request lib middle first.current.good first.current.semantic first.stored
    nextLeft nextRight nextLeftAvailable nextRightAvailable nextLeftClosed nextRightClosed
    nextLeftTyped nextRightTyped nextFuel nextResult after nextActual
  exact ⟨first, next⟩

end MicroCFTA.SourceSynthesisNativeTypeWarmRequests
