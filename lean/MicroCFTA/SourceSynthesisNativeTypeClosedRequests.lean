import MicroCFTA.SourceSynthesisNativeTypeTrace
import MicroCFTA.SourceCurrentAllocatedNativeActualScope

/-!
# Closed actual native Type requests at warm states

The joint state retains physical readiness, semantic readiness, scoped memo
results, idle memo tables, and conditional Type-origin stores. An original
accepted build derives its cold certificate. An actual completed request
returns this certificate and a closed result at the same physical state.

Type origin records guard provenance. It does not bound generated guards.
Available closed annotated operands and completed execution remain local
premises. These laws do not establish those roles at every worker request,
trace existence, failure-prefix invariants, or a global resource bound.
-/
namespace MicroCFTA.SourceSynthesisNativeTypeClosedRequests
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisFirstOrderConstruction
open SourceSynthesisNativeTypeTrace (Origin cold origin_top origin_conjoin)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Good" => SourceCurrentAllocatedNativePhysicalCompletion.Good
local notation "SemanticReady" => SourceEqualityRequiredSemanticCache.SemanticReady
local notation "Stored" => SourceCurrentHereditaryNativeUniversalStore.Stored

/-- These facts can be retained between actual closed Type requests. -/
structure Ready (lib : Library) (state : Checked width) : Prop where
  good : Good state
  semantic : SemanticReady state.native.machine.heap
  scopes : SourceCurrentAllocatedNativeScopeCache.Scoped state.native
  idle : SourceRecursiveIntersectionNative.Idle state.native
  stored : Stored (Origin lib) state

/-- Actual original construction derives the cold semantic and memo facts. -/
theorem cold_ready [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (accepted : firstOrderRaw lib query signed = .ok expression)
    (value : Value Symbol Guard) (heap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build
      (SourceSynthesisUniverseCallerBoundary.ordinarySymbols expression) [] empty = .done value heap)
    (width : Nat) (operations : SourceEqualityConstraintMemoAllocation.State)
    (good : Good (cold width heap operations)) :
    Ready lib (cold width heap operations) := by
  exact ⟨good,
    SourceEqualityRequiredSemanticCache.constructed
      (SourceSynthesisUniverseCallerBoundary.ordinarySymbols expression) value heap built,
    SourceCurrentAllocatedNativeScopeCache.initial_scoped width ⟨heap, Cache.emptyState⟩,
    SourceRecursiveIntersectionNative.idle_initial _,
    SourceSynthesisNativeTypeTrace.initial_stored lib query signed expression accepted
      value heap built width operations⟩

/-- The same completed request retains its full return, joint state, and closed result. -/
theorem completed [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {width : Nat} (lib : Library) (before : Checked width) (ready : Ready lib before)
    (left right : Value Symbol Guard)
    (leftAvailable : Available before.native.machine.heap left)
    (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (leftTyped : Annotated (Origin lib) left) (rightTyped : Annotated (Origin lib) right)
    (result : Value Symbol Guard) (after : Checked width)
    (actual : SourceCurrentAllocatedTargetQuery.Step left right before result after) :
    SourceCurrentHereditaryNativeGeneralInduction.Return (Origin lib)
      (source := before.native.machine.heap)
      (inventory := SourceRecursiveIntersectionSourceInventory.domains before.native.machine.heap)
      (initial := before.native.machine.domains) before after result
      (fun final output => Available final.heap output)
      (fun final output => Available final.heap output ∧ Annotated (Origin lib) output) ∧
    Ready lib after ∧ result.free = [] := by
  have scopes := SourceCurrentAllocatedNativeActualScope.step actual ready.good ready.semantic
    ready.scopes ready.idle leftAvailable rightAvailable leftClosed rightClosed
  cases actual with
  | run trace =>
    rename_i fuel
    let source := before.native.machine.heap
    let inventory := SourceRecursiveIntersectionSourceInventory.domains source
    let request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩
    have facts := ready.good.native.machine.1
    have current : SourceCurrentAllocatedRecursivePrefixState.Current source inventory
        before.native.machine.domains before :=
      SourceCurrentAllocatedRecursivePrefixState.initial source inventory before ready.good ready.semantic rfl
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
    have returned := preserves (.code (requestNode request.domain request.left request.right)) before after result _ _
      current physical (fun _ => trivial) certificate ready.stored trace
    exact ⟨returned,
      ⟨returned.current.good, returned.current.semantic, scopes.1, scopes.2.1, returned.stored⟩,
      scopes.2.2⟩

end MicroCFTA.SourceSynthesisNativeTypeClosedRequests
