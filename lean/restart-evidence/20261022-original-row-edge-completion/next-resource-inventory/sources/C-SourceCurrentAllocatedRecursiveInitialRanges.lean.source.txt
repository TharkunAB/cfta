import MicroCFTA.SourceCurrentAllocatedRecursivePrefixAdmission
import MicroCFTA.SourceCurrentAllocatedNativeColdClosedExact

/-!
# Initial resource admission for general recursive native intersection

Initial source counters and a finite domain inventory derive every reached
machine-word check. The existing recursive completion theorem then returns
the exact intersection language at the same current checked result.
-/
namespace MicroCFTA.SourceCurrentAllocatedRecursiveInitialRanges
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView IntersectSchedule SourceEqualityNativeDemand
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedRecursivePrefixState (Current)
open SourceCurrentAllocatedRecursivePrefixAdmission (Resources)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Certified" => SourceCurrentAllocatedRecursivePrefixControl.Certified
local notation "WordRanges" => SourceCurrentAllocatedNativeRequestBounds.WordRanges
local notation "DomainKey" => IntersectionFlatMemoKeyDomain.DomainKey
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
variable {bits : Nat} {source : InternedConstructorTemplates.State Symbol Guard}
variable {inventory : List DomainKey} {initialDomains : Cache.State DomainKey}

/-- Initial resources and a local source certificate derive words on every raw prefix. -/
theorem word_ranges {A : Type} (resources : Resources bits source inventory initialDomains)
    (control : Control A) (before : Checked (bits + 2)) (post : Machine Symbol Guard → A → Prop)
    (current : Current source inventory initialDomains before)
    (certificate : Certified source inventory control before.native.machine post)
    (fields : SourceCurrentAllocatedNativeFieldClosure.Fields control before) : WordRanges control before := by
  intro fuel remaining after trace
  exact (SourceCurrentAllocatedRecursivePrefixAdmission.prefixes resources fuel control before remaining after post
    current certificate fields trace).words

/-- The same initial conditions derive enter-key admission instead of assuming it over prefixes. -/
theorem domain_prefixes {A : Type} (resources : Resources bits source inventory initialDomains)
    (control : Control A) (before : Checked (bits + 2)) (post : Machine Symbol Guard → A → Prop)
    (current : Current source inventory initialDomains before)
    (certificate : Certified source inventory control before.native.machine post)
    (fields : SourceCurrentAllocatedNativeFieldClosure.Fields control before) :
    SourceCurrentAllocatedNativeDomainTrace.Prefixes inventory control before := by
  intro fuel remaining after trace
  exact (SourceCurrentAllocatedRecursivePrefixAdmission.prefixes resources fuel control before remaining after post
    current certificate fields trace).entered

/-- A cold original recursive request derives its complete range checks from initial counters. -/
theorem initial_ranges (bits : Nat) (machine : Machine Symbol Guard)
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (good : Good (⟨initial (bits + 2) machine, operations⟩ : Checked (bits + 2)))
    (semantic : SemanticReady machine.heap)
    (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available machine.heap left) (rightAvailable : Available machine.heap right)
    (nodes : machine.heap.nodes.next < 2 ^ bits) (edges : machine.heap.edges.next ≤ 2 ^ (bits + 2))
    (room : machine.domains.next + 2 ^ (machine.heap.nodes.next + machine.heap.nodes.next * machine.heap.nodes.next) <
      2 ^ (bits + 1)) :
    WordRanges (.code (requestNode IntersectionEmptyDomain.emptyDomain left right))
      (⟨initial (bits + 2) machine, operations⟩ : Checked (bits + 2)) ∧
    SourceCurrentAllocatedNativeDomainTrace.Prefixes (SourceRecursiveIntersectionSourceInventory.domains machine.heap)
      (.code (requestNode IntersectionEmptyDomain.emptyDomain left right))
      (⟨initial (bits + 2) machine, operations⟩ : Checked (bits + 2)) := by
  let inventory := SourceRecursiveIntersectionSourceInventory.domains machine.heap
  let before : Checked (bits + 2) := ⟨initial (bits + 2) machine, operations⟩
  let request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩
  have resources : Resources bits machine.heap inventory machine.domains :=
    ⟨good.native.machine.1, SourceCurrentAllocatedRecursiveDomainCode.source_closed machine.heap good.native.machine.1,
      good.native.machine.2, nodes, edges, by
        simpa only [inventory, SourceRecursiveIntersectionSourceInventory.domains_length] using room⟩
  have current : Current machine.heap inventory machine.domains before :=
    SourceCurrentAllocatedRecursivePrefixState.initial machine.heap inventory before good semantic rfl
  have scope := initial_scope machine.heap left right leftOriginal rightOriginal leftAvailable rightAvailable
  have certificate : Certified machine.heap inventory (.code (requestNode request.domain request.left request.right))
      before.native.machine (fun after value => Available after.heap value) :=
    SourceCurrentAllocatedRecursivePrefixCode.request_node machine.heap inventory request machine
      ⟨empty_domain machine, leftAvailable, rightAvailable⟩ scope
      (SourceRecursiveIntersectionSourceInventory.empty_mem machine.heap)
  exact ⟨word_ranges resources _ before _ current certificate (fun _ => trivial),
    domain_prefixes resources _ before _ current certificate (fun _ => trivial)⟩

/-- Initial counters derive finite recursive cold execution and its exact closed intersection language. -/
theorem cold_complete (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (machine : Machine Symbol Guard) (operations : SourceEqualityConstraintMemoAllocation.State)
    (good : Good (⟨initial (bits + 2) machine, operations⟩ : Checked (bits + 2)))
    (semantic : SemanticReady machine.heap)
    (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available machine.heap left) (rightAvailable : Available machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (nodes : machine.heap.nodes.next < 2 ^ bits) (edges : machine.heap.edges.next ≤ 2 ^ (bits + 2))
    (room : machine.domains.next + 2 ^ (machine.heap.nodes.next + machine.heap.nodes.next * machine.heap.nodes.next) <
      2 ^ (bits + 1)) :
    ∃ (inputModel : InputMeaning (view machine.heap (SourceEqualityPCSGuard.holds formulas solver)))
      (inputRanked : RankedInput (view machine.heap (SourceEqualityPCSGuard.holds formulas solver)) inputModel.valid)
      (fuel : Nat) (value : Value Symbol Guard) (after : Checked (bits + 2)),
      SourceCurrentAllocatedNativeContextualCompletion.Receipt
        (semanticView := view machine.heap (SourceEqualityPCSGuard.holds formulas solver)) (model := inputModel)
        (ranked := inputRanked) (semanticHolds := SourceEqualityPCSGuard.holds formulas solver)
        fuel (.code (requestNode IntersectionEmptyDomain.emptyDomain left right))
        ⟨initial (bits + 2) machine, operations⟩ value after
        (fun final value => Available final.heap value)
        (fun _ value => SourceCurrentAllocatedNativeContextCache.NodeLaw
          (view machine.heap (SourceEqualityPCSGuard.holds formulas solver)) inputModel inputRanked
          (SourceEqualityPCSGuard.holds formulas solver) ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ value) ∧
      SourceCurrentAllocatedNativeScopeCache.Scoped after.native ∧
      SourceRecursiveIntersectionNative.Idle after.native ∧ value.free = [] ∧
      ∀ output term, InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output value term ↔
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output left term ∧
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output right term := by
  exact SourceCurrentAllocatedNativeColdClosedExact.cold_complete formulas solver machine operations good semantic
    left right leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed
    (initial_ranges bits machine operations good semantic left right leftOriginal rightOriginal leftAvailable rightAvailable
      nodes edges room).1

end MicroCFTA.SourceCurrentAllocatedRecursiveInitialRanges
