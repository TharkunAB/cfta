import MicroCFTA.SourceCurrentConstrainedCapCurrentNative
import MicroCFTA.SourceCurrentAllocatedRecursiveWarmInitialRanges

/-!
# Serial checked queries with one initial source budget

Every operand belongs to the same initial physical source. Each actual
return retains that source and its complete past domain allocation history.
All later calls use the initial source counters and domain credit. Native
tables, equality operations, and global tables remain populated.
Results can be returned, but new result operands need a larger source proof.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapStaticQueries
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedRecursivePrefixAdmission (Resources)
open SourceCurrentAllocatedRecursivePrefixState (Current)
open SourceCurrentConstrainedCapCheckedJointClosed (Plain)
open SourceCurrentConstrainedCap (Cap)
open InternedNestedProvenance (Values)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "DomainKey" => IntersectionFlatMemoKeyDomain.DomainKey
local notation "domains" => SourceRecursiveIntersectionSourceInventory.domains
local notation "Native" => SourceCurrentConstrainedCapCurrentNative.At Plain
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
variable {bits : Nat} {source : Heap} {initial : Cache.State DomainKey}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Initial counters reserve the complete fixed-source domain inventory once. -/
theorem resources (facts : Facts source) (valid : Cache.Valid initial)
    (nodes : source.nodes.next < 2 ^ bits) (edges : source.edges.next ≤ 2 ^ (bits + 2))
    (room : initial.next + 2 ^ (source.nodes.next + source.nodes.next * source.nodes.next) < 2 ^ (bits + 1)) :
    Resources bits source (domains source) initial :=
  ⟨facts, SourceCurrentAllocatedRecursiveDomainCode.source_closed source facts, valid, nodes, edges,
    by simpa only [SourceRecursiveIntersectionSourceInventory.domains_length] using room⟩

private theorem certificate (before : Checked (bits + 2))
    (current : Current source (domains source) initial before)
    (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available source left) (rightAvailable : Available source right) :
    SourceCurrentAllocatedRecursivePrefixControl.Certified source (domains source)
      (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before.native.machine
      (fun after value => Available after.heap value) := by
  exact SourceCurrentAllocatedRecursivePrefixCode.request_node source (domains source)
    ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ before.native.machine
    ⟨empty_domain _, leftAvailable.grows source _ current.growth current.history,
      rightAvailable.grows source _ current.growth current.history⟩
    (initial_scope source left right leftOriginal rightOriginal leftAvailable rightAvailable)
    (SourceRecursiveIntersectionSourceInventory.empty_mem source)

/-- Later entries derive every reached word check from the same original resources. -/
theorem ranges (reserved : Resources bits source (domains source) initial)
    (before : Checked (bits + 2)) (current : Current source (domains source) initial before)
    (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available source left) (rightAvailable : Available source right) :
    SourceCurrentAllocatedNativeRequestBounds.WordRanges
      (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before := by
  exact SourceCurrentAllocatedRecursiveInitialRanges.word_ranges reserved _ before _ current
    (certificate before current left right leftOriginal rightOriginal leftAvailable rightAvailable) (fun _ => trivial)

/-- The same actual query extends the initial source and allocation history. -/
theorem retained (reserved : Resources bits source (domains source) initial)
    {before after : Checked (bits + 2)} {left right result : Value Symbol Guard}
    (current : Current source (domains source) initial before)
    (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available source left) (rightAvailable : Available source right)
    (actual : SourceCurrentAllocatedTargetQuery.Step left right before result after) :
    Current source (domains source) initial after := by
  cases actual with
  | run trace =>
      exact (SourceCurrentAllocatedRecursivePrefixAdmission.prefixes reserved _ _ before _ after _ current
        (certificate before current left right leftOriginal rightOriginal leftAvailable rightAvailable)
        (fun _ => trivial) trace.steps).current

/-- One later finite query needs no fresh numeric admission or future execution premise. -/
theorem complete (depth : Nat) (reserved : Resources bits source (domains source) initial)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (before : Checked (bits + 2))
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (current : Current source (domains source) initial before) (native : Native before)
    (left right : Value Symbol Guard) (leftAvailable : Available source left) (rightAvailable : Available source right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (leftCap : Cap Plain depth left) (rightCap : Cap Plain depth right)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ next result after,
      SourceCurrentAllocatedTargetQuery.Receipt formulas solver next left right before result after memos ∧
      Current source (domains source) initial after ∧ Native after ∧ Cap Plain depth result := by
  have leftOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original left source reserved.facts.coherent
    leftAvailable leftClosed
  have rightOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original right source reserved.facts.coherent
    rightAvailable rightClosed
  have leftNow := leftAvailable.grows source _ current.growth current.history
  have rightNow := rightAvailable.grows source _ current.growth current.history
  obtain ⟨next, result, after, _, _, receipt⟩ := SourceCurrentAllocatedTargetQuery.finite formulas solver inventory
    left right before ready admitted leftNow rightNow leftClosed rightClosed
    (ranges reserved before current left right leftOriginal rightOriginal leftAvailable rightAvailable) memos valid
  have physical := retained reserved current leftOriginal rightOriginal leftAvailable rightAvailable receipt.actual
  have joint := SourceCurrentConstrainedCapCurrentNative.step depth formulas solver receipt.actual ready.good ready.semantic
    native leftNow rightNow leftClosed rightClosed leftCap rightCap
  exact ⟨next, result, after, receipt, physical, joint.1, joint.2.1⟩

/-- A serial run retains a full literal query receipt at every actual entry. -/
inductive Queries (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (memos : Memos) :
    List (Value Symbol Guard × Value Symbol Guard) → Checked (bits + 2) →
      List (Value Symbol Guard) → Checked (bits + 2) → Prop where
  | nil : Queries formulas solver memos [] before [] before
  | cons (receipt : SourceCurrentAllocatedTargetQuery.Receipt formulas solver inventory left right before result middle memos)
      (tail : Queries formulas solver memos requests middle results after) :
      Queries formulas solver memos ((left, right) :: requests) before (result :: results) after

/-- One initial source and domain budget constructs every finite list of original queries. -/
theorem complete_many (depth : Nat) (reserved : Resources bits source (domains source) initial)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (requests : List (Value Symbol Guard × Value Symbol Guard))
    (inputs : ∀ pair ∈ requests, Available source pair.1 ∧ Available source pair.2 ∧
      pair.1.free = [] ∧ pair.2.free = [] ∧ Cap Plain depth pair.1 ∧ Cap Plain depth pair.2)
    (inventory : Inventory) (before : Checked (bits + 2))
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (current : Current source (domains source) initial before) (native : Native before)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ results after next,
      Queries formulas solver memos requests before results after ∧ Ready after ∧ At formulas solver next after ∧
      Extension before.native.machine after.native.machine ∧ Current source (domains source) initial after ∧
      Native after ∧ Values after.native.machine.heap results ∧ (∀ result ∈ results, Cap Plain depth result) ∧
      (∀ result ∈ results, result.free = []) ∧ Valid after.native.machine.heap memos ∧
      after.native.machine.domains.next ≤ initial.next + (domains source).length := by
  induction requests generalizing inventory before with
  | nil =>
      exact ⟨[], before, inventory, .nil, ready, admitted, .refl _, current, native,
        (by intro value member; cases member), (by intro value member; cases member),
        (by intro value member; cases member), valid, current.domains.next_le⟩
  | cons pair rest ih =>
      obtain ⟨leftAvailable, rightAvailable, leftClosed, rightClosed, leftCap, rightCap⟩ := inputs pair List.mem_cons_self
      obtain ⟨next, result, middle, receipt, physical, joint, cap⟩ := complete depth reserved formulas solver inventory before
        ready admitted current native pair.1 pair.2 leftAvailable rightAvailable leftClosed rightClosed leftCap rightCap memos valid
      obtain ⟨results, after, finalInventory, actual, afterReady, afterAdmitted, extension, afterPhysical, afterJoint,
          available, caps, closed, globals, domainBound⟩ :=
        ih (fun pair member => inputs pair (List.mem_cons_of_mem _ member)) next middle
          receipt.ready receipt.admitted physical joint receipt.globals
      refine ⟨result :: results, after, finalInventory, .cons receipt actual, afterReady, afterAdmitted,
        receipt.extension.trans extension, afterPhysical, afterJoint, ?_, ?_, ?_, globals, domainBound⟩
      · intro value member
        rcases List.mem_cons.mp member with rfl | member
        · exact receipt.available.grows _ _ extension.heap extension.history
        · exact available value member
      · intro value member
        rcases List.mem_cons.mp member with rfl | member
        · exact cap
        · exact caps value member
      · intro value member
        rcases List.mem_cons.mp member with rfl | member
        · exact receipt.closed
        · exact closed value member

end MicroCFTA.SourceCurrentConstrainedCapStaticQueries
