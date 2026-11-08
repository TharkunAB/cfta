import MicroCFTA.SourceSynthesisNativeTypeSites
import MicroCFTA.SourceCurrentHereditaryNativeGeneralPhysicalTrace
import MicroCFTA.SourceRecursiveIntersectionOriginalOutput

/-!
# Original Type guard origins at an actual cold native request

The literal pool excludes the Program application and filter schemas.
Original mixed heaps supply the conditional Mu store, not a Type-only heap.
The consumer retains initial physical readiness, typed closed operands, and
an actual completed checked trace as local premises. It derives the initial
stores and local certificates. It does not derive those operand roles at
every reached request, trace existence, a finite generated pool, or progress.
-/
namespace MicroCFTA.SourceSynthesisNativeTypeTrace
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax (Guard top eqGuard equalityClasses)
open SourceSynthesisFirstOrderConstruction
open SourceEqualityConstraintOrigins (Derived)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "DomainKey" => IntersectionFlatMemoKeyDomain.DomainKey

/-- Only original generalized library Types add fields beyond Top. -/
def pool (lib : Library) : List Guard :=
  top :: (lib.libraryGroups.map (fun entry => eqGuard (equalityClasses entry.2.1)) ++
    lib.libraryArgumentOnly.map (fun entry => eqGuard (equalityClasses entry.2)))

/-- Origin records actual conjunctions; its closure need not be finite. -/
def Origin (lib : Library) : Guard → Prop :=
  Derived (pool lib) top SourceEqualityPCSNativeEdge.conjoin

/-- The Type-origin predicate contains source Top. -/
theorem origin_top (lib : Library) : Origin lib top := Derived.top

/-- Actual source conjunction retains the Type-origin predicate. -/
theorem origin_conjoin (lib : Library) (first second : Guard)
    (left : Origin lib first) (right : Origin lib second) :
    Origin lib (SourceEqualityPCSNativeEdge.conjoin first second) :=
  Derived.conjunction left right

/-- This is the actual empty-domain, empty-native-table starting state. -/
def cold (width : Nat) (heap : State Symbol Guard)
    (operations : SourceEqualityConstraintMemoAllocation.State) : Checked width :=
  ⟨SourceEqualityNativeInitial.cold width heap, operations⟩

/-- The original build derives the conditional stores despite unrelated Program rows. -/
theorem initial_stored [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (accepted : firstOrderRaw lib query signed = .ok expression)
    (value : Value Symbol Guard) (heap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build
      (SourceSynthesisUniverseCallerBoundary.ordinarySymbols expression) [] empty = .done value heap)
    (width : Nat) (operations : SourceEqualityConstraintMemoAllocation.State) :
    SourceCurrentHereditaryNativeUniversalStore.Stored (Origin lib) (cold width heap operations) :=
  SourceCurrentHereditaryNativeUniversalStore.initial (Origin lib) ⟨heap, Cache.emptyState⟩ operations
    (SourceSynthesisNativeTypeSites.firstOrderRaw_muStored (Origin lib) (origin_top lib)
      lib query signed expression accepted value heap built)

/-- Actual cold Type requests preserve their origins and exact physical return facts. -/
theorem request_completed [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (accepted : firstOrderRaw lib query signed = .ok expression)
    (value : Value Symbol Guard) (heap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build
      (SourceSynthesisUniverseCallerBoundary.ordinarySymbols expression) [] empty = .done value heap)
    (width : Nat) (operations : SourceEqualityConstraintMemoAllocation.State)
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good (cold width heap operations))
    (left right : Value Symbol Guard)
    (leftAvailable : Available heap left) (rightAvailable : Available heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (leftTyped : Annotated (Origin lib) left) (rightTyped : Annotated (Origin lib) right)
    (fuel : Nat) (result : Value Symbol Guard) (after : Checked width)
    (actual : Trace fuel (.code (requestNode IntersectionEmptyDomain.emptyDomain left right))
      (cold width heap operations) (.code (.pure result)) after) :
    SourceCurrentHereditaryNativeGeneralInduction.Return (Origin lib)
      (source := heap) (inventory := SourceRecursiveIntersectionSourceInventory.domains heap)
      (initial := Cache.emptyState) (cold width heap operations) after result
      (fun final output => Available final.heap output)
      (fun final output => Available final.heap output ∧ Annotated (Origin lib) output) := by
  have verified := InternedFreshOrdinaryFacts.closed_verified
    (SourceSynthesisUniverseCallerBoundary.ordinarySymbols expression)
  have facts : InternedNestedFacts.Facts heap := by
    simpa only [built, Outcome.state] using verified.facts
  have semantic := SourceEqualityRequiredSemanticCache.constructed
    (SourceSynthesisUniverseCallerBoundary.ordinarySymbols expression) value heap built
  let inventory := SourceRecursiveIntersectionSourceInventory.domains heap
  let before := cold width heap operations
  let request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩
  have current : SourceCurrentAllocatedRecursivePrefixState.Current heap inventory Cache.emptyState before :=
    SourceCurrentAllocatedRecursivePrefixState.initial heap inventory before good semantic rfl
  have scope := initial_scope heap left right
    (SourceRecursiveIntersectionOriginalOutput.closed_original left heap facts.coherent leftAvailable leftClosed)
    (SourceRecursiveIntersectionOriginalOutput.closed_original right heap facts.coherent rightAvailable rightClosed)
    leftAvailable rightAvailable
  have physical : SourceCurrentAllocatedRecursivePrefixControl.Certified heap inventory
      (.code (requestNode request.domain request.left request.right)) before.native.machine
      (fun final output => Available final.heap output) :=
    SourceCurrentAllocatedRecursivePrefixCode.request_node heap inventory request before.native.machine
      ⟨SourceRecursiveIntersectionKernel.empty_domain before.native.machine, leftAvailable, rightAvailable⟩ scope
      (SourceRecursiveIntersectionSourceInventory.empty_mem heap)
  have localCertificate : SourceCurrentHereditaryNativeControl.Certified (Origin lib) heap
      (.code (requestNode request.domain request.left request.right)) before.native.machine
      (fun final output => Available final.heap output ∧ Annotated (Origin lib) output) :=
    SourceCurrentHereditaryNativeEffects.request_node (Origin lib) heap request before.native.machine
      (SourceCurrentHereditaryNativeScope.empty (Origin lib) heap) leftTyped rightTyped
  have stored := initial_stored lib query signed expression accepted value heap built width operations
  have preserves := SourceCurrentHereditaryNativeGeneralPhysicalTrace.completed
    (source := heap) (inventory := inventory) (initial := Cache.emptyState) (width := width)
    (A := Value Symbol Guard)
    (Origin lib) (origin_top lib) (origin_conjoin lib) facts
    (SourceCurrentAllocatedRecursiveDomainCode.source_closed heap facts) fuel
  exact preserves (.code (requestNode request.domain request.left request.right)) before after result _ _
    current physical (fun _ => trivial) localCertificate stored actual

end MicroCFTA.SourceSynthesisNativeTypeTrace
