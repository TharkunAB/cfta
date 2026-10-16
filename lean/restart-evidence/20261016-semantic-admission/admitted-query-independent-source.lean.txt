import MicroCFTA.SourceCurrentAllocatedNativeContextRebase
import MicroCFTA.SourceCurrentAllocatedNativeGrownInventory
import MicroCFTA.SourceCurrentAllocatedNativeWarmQuery

/-!
# Exact next queries after actual input inventory growth

The actual current heap admits the old roots and both next operands.
Record growth derives rank agreement on the old admitted domain.
Old request and seen-pair coverage transport the same warm cache cells.
The checked query then returns the exact closed intersection language.
Coverage of old cells remains explicit. This result does not derive
coverage of new internal requests for a later inventory expansion.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeAdmittedQuery
open Cache Language IntersectSchedule InternedConstructorTemplates
open InternedProbeProvenance InternedNestedProvenance
open SourceRecursiveIntersectionInputView
open SourceCurrentAllocatedNativeContextRebase

/-- Actual heap and root growth derive the local agreement used by warm cache transport. -/
theorem inventory_agreement {Symbol Guard : Type}
    (source target : State Symbol Guard)
    (sourceFacts : InternedNestedFacts.Facts source) (targetFacts : InternedNestedFacts.Facts target)
    (growth : Grows source target) (history : Extends source.nodes.issued target.nodes.issued)
    (holds : Guard → Term Symbol → Bool)
    (roots : List (Value Symbol Guard)) (originals : ∀ root ∈ roots, Original root)
    (available : Values source roots) (closed : ∀ root ∈ roots, root.free = [])
    (targetRoots : List (Value Symbol Guard)) (targetAvailable : Values target targetRoots)
    (targetClosed : ∀ root ∈ targetRoots, root.free = [])
    (included : ∀ root ∈ roots, root ∈ targetRoots) :
    Agreement
      (SourceCurrentAllocatedNativeInputInventoryModels.finiteInput source sourceFacts holds roots originals available closed)
      (SourceCurrentAllocatedNativeInputInventoryModels.finiteInput target targetFacts holds targetRoots
        (SourceCurrentAllocatedNativeGrownInventory.closed_originals target targetFacts targetRoots targetAvailable targetClosed)
        targetAvailable targetClosed) :=
  ⟨SourceCurrentAllocatedNativeGrownInventory.valid_grows source target sourceFacts targetFacts growth history
      holds roots originals available closed targetRoots targetAvailable targetClosed included,
    SourceCurrentAllocatedNativeGrownInventory.rank_exact source target sourceFacts targetFacts growth history
      holds roots originals available closed targetRoots targetAvailable targetClosed included⟩

local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State

section Query
variable {width : Nat}
  (source : State Symbol Guard) (sourceFacts : InternedNestedFacts.Facts source)
  (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
  (roots : List (Value Symbol Guard)) (originals : ∀ root ∈ roots, Original root)
  (available : Values source roots) (closed : ∀ root ∈ roots, root.free = [])
local notation "holds" => SourceEqualityPCSGuard.holds formulas solver
local notation "oldView" => view source holds
local notation "oldInputs" => SourceCurrentAllocatedNativeInputInventoryModels.finiteInput
  source sourceFacts holds roots originals available closed

/-- Closed current operands enter an actual larger model before the same warm checked query. -/
theorem query_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (state : Checked width) (good : SourceCurrentAllocatedNativePhysicalCompletion.Good state)
    (contextual : SourceCurrentAllocatedNativeContextCache.Contextual oldView
      (finiteInputMeaning oldView oldInputs) (finiteRankedInput oldView oldInputs) holds state.native)
    (admitted : SourceCurrentAllocatedNativeInputModelTransport.Admitted oldView
      (finiteInputMeaning oldView oldInputs) state.native)
    (seen : SeenAdmitted oldInputs state.native)
    (scopedCache : SourceCurrentAllocatedNativeScopeCache.Scoped state.native)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady state.native.machine.heap)
    (idle : SourceRecursiveIntersectionNative.Idle state.native)
    (growth : Grows source state.native.machine.heap)
    (history : Extends source.nodes.issued state.native.machine.heap.nodes.issued)
    (left right : Value Symbol Guard)
    (leftAvailable : Available state.native.machine.heap left)
    (rightAvailable : Available state.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (ranges : SourceCurrentAllocatedNativeRequestBounds.WordRanges
      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) state) :
    ∃ inputs : FiniteInput (view state.native.machine.heap holds),
      ∃ fuel value after, SourceCurrentAllocatedNativeWarmQuery.Receipt
        state.native.machine.heap formulas solver inputs fuel left right state value after := by
  let target := state.native.machine.heap
  have facts : InternedNestedFacts.Facts target := good.native.machine.1
  let targetRoots := roots ++ [left, right]
  have targetAvailable : Values target targetRoots := by
    intro root member
    change root ∈ roots ++ [left, right] at member
    rcases List.mem_append.mp member with old | next
    · exact (available root old).grows source target growth history
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at next
      rcases next with rfl | rfl
      · exact leftAvailable
      · exact rightAvailable
  have targetClosed : ∀ root ∈ targetRoots, root.free = [] := by
    intro root member
    change root ∈ roots ++ [left, right] at member
    rcases List.mem_append.mp member with old | next
    · exact closed root old
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at next
      rcases next with rfl | rfl
      · exact leftClosed
      · exact rightClosed
  have included : ∀ root ∈ roots, root ∈ targetRoots := by
    intro root member
    exact List.mem_append.mpr (Or.inl member)
  let inputs := SourceCurrentAllocatedNativeInputInventoryModels.finiteInput target facts holds targetRoots
    (SourceCurrentAllocatedNativeGrownInventory.closed_originals target facts targetRoots targetAvailable targetClosed)
    targetAvailable targetClosed
  have agreement : Agreement oldInputs inputs := inventory_agreement source target sourceFacts facts growth history holds
    roots originals available closed targetRoots targetAvailable targetClosed included
  have retained := SourceCurrentAllocatedNativeContextRebase.contextual agreement holds state.native admitted seen contextual
  have leftMember : left ∈ targetRoots := by simp [targetRoots]
  have rightMember : right ∈ targetRoots := by simp [targetRoots]
  have leftOriginal := SourceCurrentAllocatedNativeGrownInventory.closed_originals
    target facts targetRoots targetAvailable targetClosed left leftMember
  have rightOriginal := SourceCurrentAllocatedNativeGrownInventory.closed_originals
    target facts targetRoots targetAvailable targetClosed right rightMember
  have leftValid := SourceCurrentAllocatedNativeGrownInventory.target_root_valid
    target facts holds targetRoots targetAvailable targetClosed left leftMember
  have rightValid := SourceCurrentAllocatedNativeGrownInventory.target_root_valid
    target facts holds targetRoots targetAvailable targetClosed right rightMember
  obtain ⟨fuel, value, after, receipt⟩ := SourceCurrentAllocatedNativeWarmQuery.query_complete
    target facts formulas solver inputs state good retained scopedCache semantic idle
    (grows_refl target) (extends_refl target.nodes.issued) left right leftOriginal rightOriginal
    leftAvailable rightAvailable leftClosed rightClosed leftValid rightValid ranges
  exact ⟨inputs, fuel, value, after, receipt⟩
end Query
end MicroCFTA.SourceCurrentAllocatedNativeAdmittedQuery
