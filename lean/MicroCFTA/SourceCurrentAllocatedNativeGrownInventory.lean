import MicroCFTA.SourceCurrentAllocatedNativeInputGrowthModels
import MicroCFTA.SourceRecursiveIntersectionOriginalOutput

/-!
# Original input inventories in a grown constructor heap

Actual record and issued-map growth retain reachability from the old roots.
A target inventory can include these roots and new closed resident values.
Old admitted inputs retain each exact derivation rank and their language.
These results do not transport warm contextual caches or assert agreement
at identities outside the old admitted domain.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeGrownInventory
open Cache Language IntersectSchedule InternedConstructorTemplates
open InternedProbeProvenance InternedNestedProvenance
open SourceRecursiveIntersectionInputView
variable {Symbol Guard : Type}

/-- Closed resident target roots have original syntax in their actual coherent heap. -/
theorem closed_originals (target : State Symbol Guard) (facts : InternedNestedFacts.Facts target)
    (roots : List (Value Symbol Guard)) (available : Values target roots)
    (closed : ∀ root ∈ roots, root.free = []) : ∀ root ∈ roots, Original root :=
  fun root member => SourceRecursiveIntersectionOriginalOutput.closed_original root target facts.coherent
    (available root member) (closed root member)

private theorem reach_agreement {before after : View Symbol} (inputs : FiniteInput before)
    (same : ViewAgreement before after inputs.valid) (root input : Input)
    (valid : inputs.valid root) (actual : InputReach before root input) :
    inputs.valid input ∧ InputReach after root input := by
  induction actual with
  | root => exact ⟨valid, .root⟩
  | body _ ih =>
      refine ⟨inputs.body_valid _ ih.1, ?_⟩
      rw [← same.body _ ih.1]
      exact .body ih.2
  | child _ member inside ih =>
      exact ⟨inputs.row_valid _ ih.1 _ member _ inside,
        .child ih.2 (by simpa only [same.rows _ ih.1] using member) inside⟩
  | member _ member ih =>
      exact ⟨inputs.union_valid _ ih.1 _ member,
        .member ih.2 (by simpa only [same.members _ ih.1] using member)⟩
  | reference _ ih => exact ⟨inputs.reference_valid _ ih.1, .reference ih.2⟩

/-- Actual heap growth retains every input reachable from the same old closed roots. -/
theorem reachable_grows (source target : State Symbol Guard)
    (sourceFacts : InternedNestedFacts.Facts source) (targetFacts : InternedNestedFacts.Facts target)
    (growth : Grows source target) (history : Extends source.nodes.issued target.nodes.issued)
    (holds : Guard → Term Symbol → Bool) (roots : List (Value Symbol Guard))
    (originals : ∀ root ∈ roots, Original root) (available : Values source roots)
    (closed : ∀ root ∈ roots, root.free = []) (input : Input)
    (reached : SourceCurrentAllocatedNativeInputInventoryModels.Reachable source holds roots input) :
    SourceCurrentAllocatedNativeInputInventoryModels.Reachable target holds roots input := by
  obtain ⟨root, member, actual⟩ := reached
  let inputs := SourceCurrentAllocatedNativeInputInventoryModels.finiteInput
    source sourceFacts holds roots originals available closed
  have same := SourceCurrentAllocatedNativeInputGrowthModels.inventory_agreement
    source target sourceFacts targetFacts growth history holds roots originals available closed
  have valid : inputs.valid (inputOf root) :=
    SourceCurrentAllocatedNativeInputInventoryModels.root_valid
      source sourceFacts holds roots originals available closed root member
  exact ⟨root, member, (reach_agreement inputs same (inputOf root) input valid actual).2⟩

section Inventories
variable (source target : State Symbol Guard)
  (sourceFacts : InternedNestedFacts.Facts source) (targetFacts : InternedNestedFacts.Facts target)
  (growth : Grows source target) (history : Extends source.nodes.issued target.nodes.issued)
  (holds : Guard → Term Symbol → Bool)
  (roots : List (Value Symbol Guard)) (originals : ∀ root ∈ roots, Original root)
  (available : Values source roots) (closed : ∀ root ∈ roots, root.free = [])
  (targetRoots : List (Value Symbol Guard)) (targetAvailable : Values target targetRoots)
  (targetClosed : ∀ root ∈ targetRoots, root.free = [])
  (included : ∀ root ∈ roots, root ∈ targetRoots)

local notation "oldInputs" => SourceCurrentAllocatedNativeInputInventoryModels.finiteInput
  source sourceFacts holds roots originals available closed
local notation "newInputs" => SourceCurrentAllocatedNativeInputInventoryModels.finiteInput
  target targetFacts holds targetRoots (closed_originals target targetFacts targetRoots targetAvailable targetClosed)
    targetAvailable targetClosed

include growth history included

/-- The actual larger target inventory admits every old valid input. -/
theorem valid_grows (input : Input) (valid : (oldInputs).valid input) : (newInputs).valid input := by
  obtain ⟨root, member, reached⟩ := reachable_grows
    source target sourceFacts targetFacts growth history holds roots originals available closed input valid
  exact ⟨root, included root member, reached⟩

/-- Every old admitted input retains the same rank in the actual target inventory. -/
theorem rank_exact (input : Input) (valid : (oldInputs).valid input) (rank : Nat) (term : Term Symbol) :
    inputAt (finiteRanks (view target holds) newInputs) input rank term ↔
      inputAt (finiteRanks (view source holds) oldInputs) input rank term := by
  have targetValid := valid_grows source target sourceFacts targetFacts growth history holds
    roots originals available closed targetRoots targetAvailable targetClosed included input valid
  rw [finiteRanks_exact (view target holds) newInputs input targetValid rank term,
    finiteRanks_exact (view source holds) oldInputs input valid rank term]
  exact SourceCurrentAllocatedNativeInputGrowthModels.derivation_exact oldInputs
    (SourceCurrentAllocatedNativeInputGrowthModels.inventory_agreement source target sourceFacts targetFacts
      growth history holds roots originals available closed) input valid rank term

/-- Erasing the rank retains exactly the old admitted input language. -/
theorem language_exact (input : Input) (valid : (oldInputs).valid input) (term : Term Symbol) :
    inputLanguage (finiteLanguages (view target holds) newInputs) input term ↔
      inputLanguage (finiteLanguages (view source holds) oldInputs) input term := by
  have targetValid := valid_grows source target sourceFacts targetFacts growth history holds
    roots originals available closed targetRoots targetAvailable targetClosed included input valid
  rw [finiteLanguages_exact (view target holds) newInputs input targetValid term,
    finiteLanguages_exact (view source holds) oldInputs input valid term]
  exact exists_congr fun rank => SourceCurrentAllocatedNativeInputGrowthModels.derivation_exact oldInputs
    (SourceCurrentAllocatedNativeInputGrowthModels.inventory_agreement source target sourceFacts targetFacts
      growth history holds roots originals available closed) input valid rank term

/-- The identity of an old admitted nonempty input retains each exact rank. -/
theorem name_rank_exact (input : Input) (valid : (oldInputs).valid input) (nonempty : input ≠ .empty)
    (rank : Nat) (term : Term Symbol) :
    finiteRanks (view target holds) newInputs (identity input) rank term ↔
      finiteRanks (view source holds) oldInputs (identity input) rank term := by
  have same := rank_exact source target sourceFacts targetFacts growth history holds
    roots originals available closed targetRoots targetAvailable targetClosed included input valid rank term
  cases input with
  | empty => exact False.elim (nonempty rfl)
  | ref name | node name | mu name | union name => exact same

/-- The identity of an old admitted nonempty input retains its erased language. -/
theorem name_language_exact (input : Input) (valid : (oldInputs).valid input) (nonempty : input ≠ .empty)
    (term : Term Symbol) :
    finiteLanguages (view target holds) newInputs (identity input) term ↔
      finiteLanguages (view source holds) oldInputs (identity input) term := by
  have same := language_exact source target sourceFacts targetFacts growth history holds
    roots originals available closed targetRoots targetAvailable targetClosed included input valid term
  cases input with
  | empty => exact False.elim (nonempty rfl)
  | ref name | node name | mu name | union name => exact same
end Inventories

/-- A newly listed closed resident root is admitted by the actual target inventory. -/
theorem target_root_valid (target : State Symbol Guard) (facts : InternedNestedFacts.Facts target)
    (holds : Guard → Term Symbol → Bool) (roots : List (Value Symbol Guard))
    (available : Values target roots) (closed : ∀ root ∈ roots, root.free = [])
    (root : Value Symbol Guard) (member : root ∈ roots) :
    (SourceCurrentAllocatedNativeInputInventoryModels.finiteInput target facts holds roots
      (closed_originals target facts roots available closed) available closed).valid (inputOf root) :=
  SourceCurrentAllocatedNativeInputInventoryModels.root_valid target facts holds roots
    (closed_originals target facts roots available closed) available closed root member

end MicroCFTA.SourceCurrentAllocatedNativeGrownInventory
