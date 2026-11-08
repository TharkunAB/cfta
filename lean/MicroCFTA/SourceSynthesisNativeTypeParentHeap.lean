import MicroCFTA.SourceSynthesisNativeTypeSharedState
import MicroCFTA.SourceCurrentAllocatedMkEdge
import MicroCFTA.SourceCurrentParentGuardHeapReturns

/-!
# Type states at actual Parent row construction

The constructor receipt records the actual result, physical effects, and
unchanged native tables and domains. It does not supply a Type store.
The causal guard profile derives that store at the returned heap. Equality
operations can change. Warm Merge entries remain available after extension.

Row guards can be Program guards. No annotation predicate is imposed on
all row guards. The receipt retains the same source acceptance test for
the full guard and children. These local laws do not prove all reached
Parent inputs, failure preservation, completion, or resource bounds.
-/
namespace MicroCFTA.SourceSynthesisNativeTypeParentHeap
open InternedConstructorTemplates InternedProbeProvenance
open MergedColdReaderClosedInputs (ClosedValues)
open SourceSynthesisTypeSyntax (Library)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceRecursiveIntersectionKernel (Extension)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentAllocatedSharedTargetState (initial)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Ready" => SourceSynthesisNativeTypeSharedState.Ready
local notation "GuardHeap" => SourceCurrentConstrainedCapGuardHeap.Heap
local notation "Effects" => SourceCurrentConjunctionRowsAllocation.Effects
variable {width : Nat}

private theorem same_native (before after : Checked width)
    (nodes : after.native.nodes = before.native.nodes)
    (edges : after.native.edges = before.native.edges)
    (domains : after.native.machine.domains = before.native.machine.domains) :
    after = advancePhysical before (physical after) := by
  rcases before with ⟨⟨⟨oldHeap, oldDomains⟩, oldNodes, oldEdges⟩, oldOperations⟩
  rcases after with ⟨⟨⟨newHeap, newDomains⟩, newNodes, newEdges⟩, newOperations⟩
  change newNodes = oldNodes at nodes
  change newEdges = oldEdges at edges
  change newDomains = oldDomains at domains
  cases nodes
  cases edges
  cases domains
  rfl

private theorem advance (lib : Library) {before after : Checked width} {memo : Memo}
    (ready : Ready lib (initial before memo))
    (effects : Effects (physical before) (physical after))
    (nodes : after.native.nodes = before.native.nodes)
    (edges : after.native.edges = before.native.edges)
    (domains : after.native.machine.domains = before.native.machine.domains)
    (guards : GuardHeap (Origin lib) after.native.machine.heap) :
    Ready lib (initial after memo) ∧ Extension before.native.machine after.native.machine := by
  have previous := SourceCurrentHereditaryNativeUniversalStore.advance (Origin lib) before
    {before.native.machine with heap := after.native.machine.heap} ready.checked.stored
    (SourceCurrentConstrainedCapGuardNative.stored (Origin lib) after.native.machine.heap guards)
  have stored : SourceCurrentHereditaryNativeUniversalStore.Stored (Origin lib)
      (advancePhysical before (physical after)) := ⟨previous.constructors, previous.native⟩
  have nextReady : SourceSynthesisNativeTypeClosedRequests.Ready lib
      (advancePhysical before (physical after)) :=
    ⟨SourceCurrentAllocatedConjunctionMemo.advance_good before _ ready.checked.good effects,
      effects.ready.semantic,
      SourceCurrentAllocatedConjunctionMemo.advance_scoped before _ ready.checked.scopes,
      SourceCurrentAllocatedConjunctionMemo.advance_idle before _ ready.checked.idle, stored⟩
  have extension := SourceCurrentAllocatedQueryMemo.advance_extension before (physical after) effects
  have next : Ready lib (initial (advancePhysical before (physical after)) memo) :=
    SourceSynthesisNativeTypeSharedState.advance lib (initial before memo) _ ready nextReady
      effects.ready.costs extension
  have same := same_native before after nodes edges domains
  rw [← same] at next extension
  exact ⟨next, extension⟩

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- The actual completed constructor retains Type stores, closed children and warm state. -/
theorem build (lib : Library)
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
    {symbol : Symbol} {loaded : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula}
    {children : List (Value Symbol Guard)} {before after : Checked width}
    {result : EdgeValue Symbol Guard} {memo : Memo}
    (receipt : SourceCurrentAllocatedMkEdge.Receipt formulas solver inventory symbol loaded children before result after)
    (ready : Ready lib (initial before memo))
    (guards : GuardHeap (Origin lib) before.native.machine.heap) (closed : ClosedValues children) :
    Ready lib (initial after memo) ∧ Extension before.native.machine after.native.machine ∧
      InternedEdgeResidency.EdgeResident after.native.machine.heap result ∧ ClosedValues result.children ∧
      GuardHeap (Origin lib) after.native.machine.heap := by
  have retained := SourceCurrentParentGuardHeapReturns.build (Origin lib) receipt.actual guards
  obtain ⟨next, extension⟩ := advance lib ready receipt.effects receipt.nodes receipt.edges receipt.domains retained
  have resultClosed : ClosedValues result.children := by
    rw [receipt.children]
    split
    · exact closed
    · intro value member
      cases List.mem_singleton.mp member
      rfl
  exact ⟨next, extension, receipt.resident, resultClosed, retained⟩

/-- The actual rejection sentinel retains Type stores and has one closed Empty child. -/
theorem reject (lib : Library)
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
    {symbol : Symbol} {before after : Checked width} {result : EdgeValue Symbol Guard} {memo : Memo}
    (receipt : SourceCurrentAllocatedMkEdge.RejectReceipt formulas solver inventory symbol before result after)
    (ready : Ready lib (initial before memo))
    (guards : GuardHeap (Origin lib) before.native.machine.heap) :
    Ready lib (initial after memo) ∧ Extension before.native.machine after.native.machine ∧
      InternedEdgeResidency.EdgeResident after.native.machine.heap result ∧ ClosedValues result.children ∧
      GuardHeap (Origin lib) after.native.machine.heap := by
  have retained : GuardHeap (Origin lib) after.native.machine.heap := by
    have checked := SourceCurrentParentGuardHeapReturns.reject (Origin lib) symbol before guards
    simpa only [receipt.actual] using checked
  obtain ⟨next, extension⟩ := advance lib ready receipt.effects receipt.nodes receipt.edges receipt.domains retained
  have resultClosed : ClosedValues result.children := by
    rw [receipt.children]
    intro value member
    cases List.mem_singleton.mp member
    rfl
  exact ⟨next, extension, receipt.resident, resultClosed, retained⟩

end MicroCFTA.SourceSynthesisNativeTypeParentHeap
