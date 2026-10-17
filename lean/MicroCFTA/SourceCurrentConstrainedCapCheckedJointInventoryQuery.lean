import MicroCFTA.SourceCurrentConstrainedCapCheckedJointOriginTrace
import MicroCFTA.SourceCurrentConstrainedCapCheckedJointRebase
import MicroCFTA.SourceCurrentConstrainedCapCheckedJointWarm
import MicroCFTA.SourceCurrentAllocatedNativeInventoryRebase

/-!
# Joint checked queries over growing finite input inventories

The inventory and joint memo laws rebase at the same actual query entry.
Initial entry counters derive all request word checks. The fixed-model
query constructs its own finite return. Its actual trace derives joint
result laws and origins for all newly published cells.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapCheckedJointInventoryQuery
open Cache Language IntersectSchedule InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentConstrainedCapKernelJoint (Context)
open SourceCurrentConstrainedCapCheckedJointClosed (Plain)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Origins" => SourceCurrentConstrainedCapCheckedJointOrigins.Stored
local notation "Joint" => SourceCurrentConstrainedCapCheckedJointCache.Stored
variable {width : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- One actual query retains its computed semantic model, joint laws, and all captured request origins. -/
structure Receipt (inventory : Inventory) (depth : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (fuel : Nat) (left right : Value Symbol Guard) (before : Checked width)
    (value : Value Symbol Guard) (after : Checked width) : Prop
    extends toCoveredReceipt : SourceCurrentAllocatedNativeCoveredQuery.Receipt inventory.source formulas solver
      (inventory.inputs (SourceEqualityPCSGuard.holds formulas solver)) fuel left right before value after where
  /-- The returned heap retains the semantic and guard observations. -/
  context : Context Plain inventory.source after.native.machine
  /-- Both returned memo families retain their joint laws. -/
  stored : Joint Plain inventory.source after.native
  /-- Every allocated cell retains its original request witnesses. -/
  origins : Origins inventory.source after.native
  /-- The result retains the common input guard-depth bound. -/
  cap : SourceCurrentConstrainedCap.Cap Plain depth value
  /-- Actual free and deep occurrences retain the original pair budget. -/
  classified : SourceCurrentConstrainedCapPairOccurrences.Classified
    (SourceCurrentConstrainedCapPairOccurrences.sourceWeight Plain inventory.source)
    (SourceCurrentConstrainedCapNonplainRank.pairRank Plain left right) value
  /-- The closed result has complete original physical syntax. -/
  original : Original value
  /-- The closed result contains no constructor probe. -/
  probeFree : SourceCurrentConstrainedCapNativeProbeSupport.ProbeFree value

/-- The returned inventory remains valid for the same populated native tables and equality operations. -/
theorem Receipt.inventoryAt {inventory : Inventory} {depth : Nat}
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {fuel : Nat} {left right value : Value Symbol Guard} {before after : Checked width}
    (receipt : Receipt inventory depth formulas solver fuel left right before value after) :
    At formulas solver inventory after :=
  ⟨receipt.contextual, receipt.covered, receipt.context.growth, receipt.context.history⟩

/-- A fixed-model receipt supplies its own trace for both joint laws and causal origins. -/
theorem of_receipt (inventory : Inventory) (depth : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (before : Checked width) (good : Good before) (semantic : SemanticReady before.native.machine.heap)
    (same : before.native.machine.heap = inventory.source)
    (context : Context Plain inventory.source before.native.machine)
    (stored : Joint Plain inventory.source before.native) (origins : Origins inventory.source before.native)
    (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available inventory.source left) (rightAvailable : Available inventory.source right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (leftValid : (inventory.inputs (SourceEqualityPCSGuard.holds formulas solver)).valid (inputOf left))
    (rightValid : (inventory.inputs (SourceEqualityPCSGuard.holds formulas solver)).valid (inputOf right))
    (leftCap : SourceCurrentConstrainedCap.Cap Plain depth left)
    (rightCap : SourceCurrentConstrainedCap.Cap Plain depth right)
    (fuel : Nat) (value : Value Symbol Guard) (after : Checked width)
    (receipt : SourceCurrentAllocatedNativeCoveredQuery.Receipt inventory.source formulas solver
      (inventory.inputs (SourceEqualityPCSGuard.holds formulas solver)) fuel left right before value after) :
    Receipt inventory depth formulas solver fuel left right before value after := by
  let source := inventory.source
  let holds := SourceEqualityPCSGuard.holds formulas solver
  let inputs := inventory.inputs holds
  let domains := SourceRecursiveIntersectionSourceInventory.domains source
  let request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩
  have current := SourceCurrentAllocatedRecursivePrefixState.initial source domains before good semantic same
  have scope := initial_scope source left right leftOriginal rightOriginal leftAvailable rightAvailable
  have ready : NodeReady before.native.machine request :=
    ⟨empty_domain _, leftAvailable.grows source _ context.growth context.history,
      rightAvailable.grows source _ context.growth context.history⟩
  have physical := SourceCurrentAllocatedRecursivePrefixCode.request_node source domains request before.native.machine
    ready scope (SourceRecursiveIntersectionSourceInventory.empty_mem source)
  have localCertificate : SourceCurrentConstrainedCapCheckedJointControl.Certified Plain source
      (.code (requestNode request.domain left right)) before.native.machine
      (fun _ result => SourceCurrentConstrainedCapCheckedJointCode.NodeLaw Plain source request result) :=
    fun _ _ _ _ _ law => law
  have joint := SourceCurrentConstrainedCapCheckedJointTrace.completed inventory.facts
    (SourceCurrentAllocatedRecursiveDomainCode.source_closed source inventory.facts) fuel
    (.code (requestNode request.domain left right)) before after value _ _ current physical (fun _ => trivial)
    context localCertificate stored receipt.trace
  have originalInputs : ∀ input, inputs.valid input → OriginalInput source input :=
    SourceCurrentAllocatedNativeInputInventoryModels.reachable_original source inventory.facts holds inventory.roots
      inventory.originals inventory.available inventory.closed
  have admitted : SourceCurrentAllocatedNativeAdmissionCache.NodeCovered inputs request :=
    ⟨⟨leftOriginal, rightOriginal, leftValid, rightValid⟩, SourceCurrentAllocatedNativePairAdmission.empty_seen inputs⟩
  have certificate := SourceCurrentAllocatedNativeAdmissionCode.requestNode_certified source holds inputs request
    before.native.machine scope admitted
  have captured := SourceCurrentConstrainedCapCheckedJointOriginTrace.Trace.origins source holds inputs
    inventory.facts originalInputs receipt.trace (fun final value => Available final.heap value)
    good semantic context.growth context.history (fun _ => trivial) origins certificate
  have closedInputs := SourceCurrentConstrainedCapOriginalSupport.closed_inputs source inventory.facts request.domain left right
    leftAvailable rightAvailable leftClosed rightClosed
  have law := joint.result depth (SourceCurrentConstrainedCapOriginalSupport.empty Plain source) closedInputs leftCap rightCap
  have original := SourceRecursiveIntersectionOriginalOutput.closed_original value after.native.machine.heap
    joint.context.valid.1.coherent receipt.result receipt.closed
  exact ⟨receipt, joint.context, joint.stored, captured.1, law.1, law.2.1, original,
    SourceCurrentConstrainedCapNativeProbeSupport.of_closed value receipt.closed⟩

/-- New closed resident operands construct a finite warm query after rebasing the actual earlier stores. -/
theorem generated_complete (bits depth : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (before : Checked (bits + 2)) (good : Good before)
    (current : At formulas solver inventory before)
    (semantic : SemanticReady before.native.machine.heap)
    (context : Context Plain inventory.source before.native.machine)
    (stored : Joint Plain inventory.source before.native) (origins : Origins inventory.source before.native)
    (scopedCache : SourceCurrentAllocatedNativeScopeCache.Scoped before.native)
    (idle : SourceRecursiveIntersectionNative.Idle before.native)
    (left right : Value Symbol Guard)
    (leftAvailable : Available before.native.machine.heap left) (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (leftCap : SourceCurrentConstrainedCap.Cap Plain depth left)
    (rightCap : SourceCurrentConstrainedCap.Cap Plain depth right)
    (nodes : before.native.machine.heap.nodes.next < 2 ^ bits)
    (edges : before.native.machine.heap.edges.next ≤ 2 ^ (bits + 2))
    (room : before.native.machine.domains.next +
      2 ^ (before.native.machine.heap.nodes.next + before.native.machine.heap.nodes.next * before.native.machine.heap.nodes.next) <
      2 ^ (bits + 1)) :
    let next := SourceCurrentAllocatedNativeInventoryRebase.extend inventory before.native.machine.heap good.native.machine.1
      current.growth current.history left right leftAvailable rightAvailable leftClosed rightClosed
    ∃ fuel value after, Receipt next depth formulas solver fuel left right before value after := by
  let next := SourceCurrentAllocatedNativeInventoryRebase.extend inventory before.native.machine.heap good.native.machine.1
    current.growth current.history left right leftAvailable rightAvailable leftClosed rightClosed
  have rebased := SourceCurrentAllocatedNativeInventoryRebase.rebase formulas solver inventory before good current
    left right leftAvailable rightAvailable leftClosed rightClosed
  have jointRebased := SourceCurrentConstrainedCapCheckedJointRebase.rebase Plain inventory.source before.native
    inventory.facts current.growth current.history good.native origins stored
  have nextContext : Context Plain next.source before.native.machine :=
    ⟨good.native.machine, context.semantic, context.guards, grows_refl _, extends_refl _⟩
  have leftOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original left before.native.machine.heap
    good.native.machine.1.coherent leftAvailable leftClosed
  have rightOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original right before.native.machine.heap
    good.native.machine.1.coherent rightAvailable rightClosed
  have ranges := (SourceCurrentAllocatedRecursiveWarmInitialRanges.warm_initial_ranges bits before good semantic
    left right leftOriginal rightOriginal leftAvailable rightAvailable nodes edges room).1
  obtain ⟨fuel, value, after, receipt⟩ := SourceCurrentAllocatedNativeCoveredQuery.query_complete
    next.source next.facts formulas solver (next.inputs (SourceEqualityPCSGuard.holds formulas solver)) before good
    rebased.1.contextual rebased.1.covered scopedCache semantic idle (grows_refl _) (extends_refl _)
    left right leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed rebased.2.2.2.1 rebased.2.2.2.2 ranges
  exact ⟨fuel, value, after, of_receipt next depth formulas solver before good semantic rfl nextContext
    jointRebased.1 jointRebased.2 left right leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed
    rebased.2.2.2.1 rebased.2.2.2.2 leftCap rightCap fuel value after receipt⟩

end MicroCFTA.SourceCurrentConstrainedCapCheckedJointInventoryQuery
