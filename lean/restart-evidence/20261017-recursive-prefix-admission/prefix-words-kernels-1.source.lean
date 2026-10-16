import MicroCFTA.SourceCurrentAllocatedRecursivePrefixWords

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
set_option pp.fullNames true

namespace MicroCFTA.RecursivePrefixWordChecks
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView SourceCurrentAllocatedRecursivePrefixWords
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- A literal original-input entry derives the next physical node demand from initial supplies. -/
theorem actual_enter_child_inputs [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (bits : Nat) (before : SourceEqualityNativeDemand.State (bits + 2))
    (facts : Facts before.native.machine.heap) (valid : Cache.Valid before.native.machine.domains)
    (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available before.native.machine.heap left) (rightAvailable : Available before.native.machine.heap right)
    (first second : Nat) (leftId : SourceRecursiveIntersectionControl.identity left = some first)
    (rightId : SourceRecursiveIntersectionControl.identity right = some second)
    (nodes : before.native.machine.heap.nodes.next < 2 ^ bits)
    (room : before.native.machine.domains.next +
      (SourceRecursiveIntersectionSourceInventory.domains before.native.machine.heap).length < 2 ^ (bits + 1)) :
    let actual := SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains
      IntersectionEmptyDomain.emptyKey left right first second
    let after : SourceEqualityNativeDemand.State (bits + 2) :=
      ⟨SourceRecursiveIntersectionThunks.advance before.native {before.native.machine with domains := actual.2}, before.operations⟩
    SourceCurrentAllocatedNativePhysicalExecution.Inputs
      (.code (requestNode actual.1 (SourceRecursiveIntersectionKernel.body left) (SourceRecursiveIntersectionKernel.body right))) after ∧
      after.operations = before.operations ∧ after.native.nodes = before.native.nodes ∧ after.native.edges = before.native.edges := by
  dsimp only
  let source := before.native.machine.heap
  let inventory := SourceRecursiveIntersectionSourceInventory.domains source
  let actual := SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains
    IntersectionEmptyDomain.emptyKey left right first second
  let after : SourceEqualityNativeDemand.State (bits + 2) :=
    ⟨SourceRecursiveIntersectionThunks.advance before.native {before.native.machine with domains := actual.2}, before.operations⟩
  have scope := initial_scope source left right leftOriginal rightOriginal leftAvailable rightAvailable
  have checked := SourceRecursiveIntersectionKernel.entered before.native.machine ⟨facts, valid⟩
    IntersectionEmptyDomain.emptyDomain (empty_domain _) left right leftAvailable rightAvailable first second
  have key : actual.1.key = SourceRecursiveIntersectionDomain.extend IntersectionEmptyDomain.emptyKey
      ((SourceRecursiveIntersectionEnvironment.bindings left right).map Prod.fst)
      (SourceRecursiveIntersectionControl.pair first second) :=
    (IntersectionEmptyDomain.make_correct before.native.machine.domains valid _).2.1
  have childScope := scope.mu source IntersectionEmptyDomain.emptyDomain actual.1 left right first second key
  have member := SourceRecursiveIntersectionSourceInventory.extend_mem source facts IntersectionEmptyDomain.emptyKey
    (SourceRecursiveIntersectionSourceInventory.empty_mem source) left right leftAvailable rightAvailable first second leftId rightId
  have trace : SourceRecursiveIntersectionDomainAllocation.Trace inventory before.native.machine.domains actual.2 :=
    .step (.refl _) _ member
  exact ⟨node_inputs bits source facts inventory before.native.machine.domains after _ .pure childScope checked.2.2
    trace valid nodes room (grows_refl _) (extends_refl _), rfl, rfl, rfl⟩

/-- The initial empty-domain demand needs no domain capacity, history, or future checks. -/
theorem empty_domain_without_headroom [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (bits : Nat) (before : SourceEqualityNativeDemand.State (bits + 2))
    (facts : Facts before.native.machine.heap) (left right : Value Symbol Guard)
    (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available before.native.machine.heap left) (rightAvailable : Available before.native.machine.heap right)
    (nodes : before.native.machine.heap.nodes.next < 2 ^ bits) :
    SourceCurrentAllocatedNativeRequestBounds.Words (bits + 2)
      (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) ∧
    SourceCurrentAllocatedNativePhysicalExecution.Inputs
      (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before := by
  have words := node_words_empty bits before.native.machine.heap facts left right .pure
    (initial_scope _ left right leftOriginal rightOriginal leftAvailable rightAvailable) nodes
  exact ⟨words, ⟨⟨empty_domain _, leftAvailable, rightAvailable⟩, words⟩⟩

#print axioms actual_enter_child_inputs
#check @actual_enter_child_inputs
#print axioms empty_domain_without_headroom
#check @empty_domain_without_headroom
end MicroCFTA.RecursivePrefixWordChecks
