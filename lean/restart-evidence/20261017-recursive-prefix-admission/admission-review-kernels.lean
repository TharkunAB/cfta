import MicroCFTA.SourceCurrentAllocatedRecursiveInitialRanges

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
set_option pp.fullNames true

namespace MicroCFTA.RecursiveAdmissionIndependentChecks
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceEqualityRequiredSemanticCache (SemanticReady)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Inventory" => SourceRecursiveIntersectionSourceInventory.domains
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- An original Mu and union derive all reached checks from the initial source and past execution. -/
theorem mu_union_raw_prefix (bits fuel : Nat) (before after : Checked (bits + 2))
    (muEntry unionEntry : Interned InternedBinderProtocol.NodeKey) (body depth ordinary : Value Symbol Guard)
    (members : List (Value Symbol Guard)) (unionDepth : Nat) (free : List InternedBinderProtocol.Reference)
    (bodyOriginal : Original body) (membersOriginal : ∀ value ∈ members, Original value)
    (good : Good before) (semantic : SemanticReady before.native.machine.heap)
    (leftAvailable : Available before.native.machine.heap (.mu muEntry body depth ordinary))
    (rightAvailable : Available before.native.machine.heap (.union unionEntry members unionDepth free))
    (nodes : before.native.machine.heap.nodes.next < 2 ^ bits)
    (edges : before.native.machine.heap.edges.next ≤ 2 ^ (bits + 2))
    (room : before.native.machine.domains.next +
      2 ^ (before.native.machine.heap.nodes.next +
        before.native.machine.heap.nodes.next * before.native.machine.heap.nodes.next) < 2 ^ (bits + 1))
    (remaining : Control (Value Symbol Guard))
    (raw : Steps fuel (.code (requestNode IntersectionEmptyDomain.emptyDomain
      (.mu muEntry body depth ordinary) (.union unionEntry members unionDepth free))) before remaining after) :
    SourceCurrentAllocatedNativeRequestBounds.Words (bits + 2) remaining ∧
      SourceCurrentAllocatedNativeDomainTrace.Entered (Inventory before.native.machine.heap) remaining ∧
      Good after ∧
      SourceRecursiveIntersectionDomainAllocation.Trace (Inventory before.native.machine.heap)
        before.native.machine.domains after.native.machine.domains ∧
      SourceCurrentAllocatedNativePhysicalTraceCompletion.Trace fuel
        (.code (requestNode IntersectionEmptyDomain.emptyDomain
          (.mu muEntry body depth ordinary) (.union unionEntry members unionDepth free))) before remaining after ∧
      SourceEqualityConstraintMemoAllocation.Grows before.operations after.operations := by
  let source := before.native.machine.heap
  let inventory := Inventory source
  let request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain,
    .mu muEntry body depth ordinary, .union unionEntry members unionDepth free⟩
  have resources : SourceCurrentAllocatedRecursivePrefixAdmission.Resources bits source inventory
      before.native.machine.domains :=
    ⟨good.native.machine.1,
      SourceCurrentAllocatedRecursiveDomainCode.source_closed source good.native.machine.1,
      good.native.machine.2, nodes, edges, by
        simpa only [inventory, SourceRecursiveIntersectionSourceInventory.domains_length] using room⟩
  have current := SourceCurrentAllocatedRecursivePrefixState.initial source inventory before good semantic rfl
  have scope := initial_scope source request.left request.right
    (.mu _ _ _ _ bodyOriginal) (.union _ _ _ _ membersOriginal) leftAvailable rightAvailable
  have certificate := SourceCurrentAllocatedRecursivePrefixCode.request_node source inventory request before.native.machine
    ⟨empty_domain _, leftAvailable, rightAvailable⟩ scope
    (SourceRecursiveIntersectionSourceInventory.empty_mem source)
  have receipt := SourceCurrentAllocatedRecursivePrefixAdmission.prefixes resources fuel
    (.code (requestNode request.domain request.left request.right)) before remaining after
    (fun final value => Available final.heap value) current certificate (fun _ => trivial) raw
  exact ⟨receipt.words, receipt.entered, receipt.current.good, receipt.current.domains,
    receipt.trace, receipt.operations⟩

/-- A raw completed compiler body derives its physical post at its exact returned checked state. -/
theorem original_body_return (bits fuel : Nat) (before after : Checked (bits + 2))
    (left right result : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (good : Good before) (semantic : SemanticReady before.native.machine.heap)
    (leftAvailable : Available before.native.machine.heap left) (rightAvailable : Available before.native.machine.heap right)
    (nodes : before.native.machine.heap.nodes.next < 2 ^ bits)
    (edges : before.native.machine.heap.edges.next ≤ 2 ^ (bits + 2))
    (room : before.native.machine.domains.next +
      2 ^ (before.native.machine.heap.nodes.next +
        before.native.machine.heap.nodes.next * before.native.machine.heap.nodes.next) < 2 ^ (bits + 1))
    (raw : Steps fuel (.code (compileNode ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩)) before
      (.code (.pure result)) after) :
    Available after.native.machine.heap result ∧ Good after ∧
      Extension before.native.machine after.native.machine ∧
      SourceEqualityConstraintMemoAllocation.Grows before.operations after.operations ∧
      SourceRecursiveIntersectionDomainAllocation.Trace (Inventory before.native.machine.heap)
        before.native.machine.domains after.native.machine.domains := by
  let source := before.native.machine.heap
  let inventory := Inventory source
  let request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩
  have resources : SourceCurrentAllocatedRecursivePrefixAdmission.Resources bits source inventory
      before.native.machine.domains :=
    ⟨good.native.machine.1,
      SourceCurrentAllocatedRecursiveDomainCode.source_closed source good.native.machine.1,
      good.native.machine.2, nodes, edges, by
        simpa only [inventory, SourceRecursiveIntersectionSourceInventory.domains_length] using room⟩
  have current := SourceCurrentAllocatedRecursivePrefixState.initial source inventory before good semantic rfl
  have certificate := SourceCurrentAllocatedRecursivePrefixCode.node_certified source inventory good.native.machine.1
    resources.closed request (initial_scope source left right leftOriginal rightOriginal leftAvailable rightAvailable)
    (SourceRecursiveIntersectionSourceInventory.empty_mem source) before.native.machine good.native.machine semantic
    ⟨empty_domain _, leftAvailable, rightAvailable⟩ (grows_refl _) (extends_refl _)
  have receipt := SourceCurrentAllocatedRecursivePrefixAdmission.prefixes resources fuel (.code (compileNode request)) before (.code (.pure result)) after
    (fun final value => Available final.heap value) current certificate
    (SourceCurrentAllocatedNativeCodeFields.compileNode_fields before.operations request) raw
  exact ⟨receipt.result result rfl, receipt.current.good, receipt.extension, receipt.operations, receipt.current.domains⟩

/-- Closed Mu and union roots obtain a literal finite result and exact language without a supplied range plan. -/
theorem cold_mu_union_exact (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (machine : Machine Symbol Guard) (operations : SourceEqualityConstraintMemoAllocation.State)
    (muEntry unionEntry : Interned InternedBinderProtocol.NodeKey) (body depth ordinary : Value Symbol Guard)
    (members : List (Value Symbol Guard)) (unionDepth : Nat) (free : List InternedBinderProtocol.Reference)
    (bodyOriginal : Original body) (membersOriginal : ∀ value ∈ members, Original value)
    (good : Good (⟨initial (bits + 2) machine, operations⟩ : Checked (bits + 2)))
    (semantic : SemanticReady machine.heap)
    (leftAvailable : Available machine.heap (.mu muEntry body depth ordinary))
    (rightAvailable : Available machine.heap (.union unionEntry members unionDepth free))
    (leftClosed : (Value.mu muEntry body depth ordinary).free = [])
    (rightClosed : (Value.union unionEntry members unionDepth free).free = [])
    (nodes : machine.heap.nodes.next < 2 ^ bits) (edges : machine.heap.edges.next ≤ 2 ^ (bits + 2))
    (room : machine.domains.next + 2 ^ (machine.heap.nodes.next + machine.heap.nodes.next * machine.heap.nodes.next) <
      2 ^ (bits + 1)) :
    ∃ fuel value after,
      execute fuel (.code (requestNode IntersectionEmptyDomain.emptyDomain
        (.mu muEntry body depth ordinary) (.union unionEntry members unionDepth free)))
        (⟨initial (bits + 2) machine, operations⟩ : Checked (bits + 2)) = .done value after ∧
      Good after ∧ SourceCurrentAllocatedNativeScopeCache.Scoped after.native ∧
      SourceRecursiveIntersectionNative.Idle after.native ∧ value.free = [] ∧
      ∀ output term, InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output value term ↔
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output
          (.mu muEntry body depth ordinary) term ∧
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output
          (.union unionEntry members unionDepth free) term := by
  obtain ⟨_, _, fuel, value, after, receipt, keptScope, idle, closed, exactLanguage⟩ :=
    SourceCurrentAllocatedRecursiveInitialRanges.cold_complete bits formulas solver machine operations good semantic
      (.mu muEntry body depth ordinary) (.union unionEntry members unionDepth free)
      (.mu _ _ _ _ bodyOriginal) (.union _ _ _ _ membersOriginal) leftAvailable rightAvailable leftClosed rightClosed
      nodes edges room
  exact ⟨fuel + 1, value, after, receipt.done, receipt.good, keptScope, idle, closed, exactLanguage⟩

#print axioms mu_union_raw_prefix
#check @mu_union_raw_prefix
#print axioms original_body_return
#check @original_body_return
#print axioms cold_mu_union_exact
#check @cold_mu_union_exact
end MicroCFTA.RecursiveAdmissionIndependentChecks
