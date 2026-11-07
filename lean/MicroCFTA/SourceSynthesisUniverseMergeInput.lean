import MicroCFTA.SourceSynthesisUniversePrepared
import MicroCFTA.MergedPrefixCompletion
import MicroCFTA.SourceMemoGate

/-!
# Complete merging after original synthesis construction

Original signed requests derive the actual input, heap, and preparation.
Complete source merging adds at most one ordinary or union prefix layer.
Every output atom is the same actual universe atom as in the input.
The comparison bound stabilizes the complete result and returned heap.
This result does not bound the complete enumeration driver or native work.
-/
namespace MicroCFTA.SourceSynthesisUniverseMergeInput
open InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedBoundaryAtoms SourceSynthesisTypeSyntax InternedShallowHeap
open SourceSynthesisGeneralizeSyntax (Guard top)

variable [DecidableEq (EdgeKey String Guard)]

/-- Original requests derive a complete merge, its height bound, and its actual universe records. -/
theorem firstOrderRaw_merge_prefix_bound (lib : Library) (query : Query) (size : Int) :
    match SourceSynthesisFirstOrderConstruction.firstOrderRaw lib query size with
    | .error _ => True
    | .ok expression =>
        ∃ input before bound result after,
          InternedFreshOrdinaryConstruction.build expression [] empty = .done input before ∧
          Facts before ∧ Available before input ∧ MergedPhysicalWarmup.Prepared before ∧
          SourceSynthesisUniversePrefixHeight.height input ≤ sizeOf expression ∧
          (∀ fuel, bound ≤ fuel → MergedColdMerge.execute MergedSourceGrouping.groups
            SourceMemoGate.plain top fuel input before = .done result after) ∧
          (∀ fuel, NoNewMu before (MergedColdMerge.execute MergedSourceGrouping.groups
            SourceMemoGate.plain top fuel input before).state ∧
            Shallow (MergedColdMerge.execute MergedSourceGrouping.groups
              SourceMemoGate.plain top fuel input before).state) ∧
          MergedColdMerge.Extension before after ∧ NoNewMu before after ∧ Available after result ∧
          SourceSynthesisUniversePrefixHeight.height result ≤ sizeOf expression + 1 ∧
          (atoms result = [] ∨ ∃ entry body depth ordinary,
            Available after (.mu entry body depth ordinary) ∧
            SourceSynthesisUniverseBody.Shape top
              (SourceSynthesisFirstOrderConstruction.constructorCatalog lib query) (.interned entry.identity) body ∧
            SourceSynthesisUniverseResidentRows.Rows top
              (SourceSynthesisFirstOrderConstruction.constructorCatalog lib query) (.interned entry.identity) body after ∧
            SourceSynthesisUniverseResidentRows.Rows top
              (SourceSynthesisFirstOrderConstruction.constructorCatalog lib query) .depth depth after ∧
            SourceSynthesisUniverseResidentRows.Rows top
              (SourceSynthesisFirstOrderConstruction.constructorCatalog lib query)
              (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) ordinary after ∧
            ∀ item ∈ atoms result, item = .mu entry.identity) := by
  cases returned : SourceSynthesisFirstOrderConstruction.firstOrderRaw lib query size with
  | error => trivial
  | ok expression =>
      have source := SourceSynthesisUniversePrefixConstruction.firstOrderRaw_physical_prefix_bound lib query size
      rw [returned] at source
      obtain ⟨input, before, built, facts, available, heightBound, boundary⟩ := source
      have derived := SourceSynthesisUniversePrepared.firstOrderRaw_prepared lib query size
      rw [returned] at derived
      obtain ⟨sameInput, sameHeap, sameBuilt, _facts, _available, shallow, prepared, _height⟩ := derived
      rw [built] at sameBuilt
      cases sameBuilt
      obtain ⟨bound, result, after, complete, extension, resultAvailable, unchanged, resultHeight, origin⟩ :=
        MergedPrefixCompletion.source_execute_prefix_complete SourceMemoGate.plain top input before
          facts prepared available
      refine ⟨input, before, bound, result, after, built, facts, available, prepared, heightBound,
        complete, ?_, extension, unchanged, resultAvailable,
        Nat.le_trans resultHeight (Nat.add_le_add_right heightBound 1), ?_⟩
      · intro fuel
        have retained := MergedNoNewMu.source_execute_noNewMu SourceMemoGate.plain top fuel input before
          facts prepared available
        exact ⟨retained, shallow_preserved before _ shallow retained⟩
      · rcases boundary with noAtoms | ⟨entry, body, depth, ordinary, muAvailable, shape, bodyRows, depthRows,
          ordinaryRows, onlyMu⟩
        · left
          cases output : atoms result with
          | nil => rfl
          | cons first rest =>
              have member := origin first (by simp only [output, List.mem_cons_self])
              simp only [noAtoms, List.not_mem_nil] at member
        · right
          exact ⟨entry, body, depth, ordinary, extension.available _ muAvailable, shape,
            bodyRows.grows extension.growth, depthRows.grows extension.growth, ordinaryRows.grows extension.growth,
            fun item member => onlyMu item (origin item member)⟩

end MicroCFTA.SourceSynthesisUniverseMergeInput
