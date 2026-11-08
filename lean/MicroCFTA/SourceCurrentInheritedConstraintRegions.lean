import MicroCFTA.SourceEqualityConstraintRegions
import MicroCFTA.SourceCurrentOuterRowFieldOrigins

/-!
# Endpoint regions through the current allocated inherited prefix

Actual returned fields retain the original guard or the Top sentinel.
The allocated accessor and combiner retain literal physical payloads.
These laws preserve supplied endpoint regions through those operations.
Original synthesis occurrence roles remain a separate derivation.
-/
namespace MicroCFTA.SourceCurrentInheritedConstraintRegions
open EqualityNormalize
open SourceEqualityConstraintRegions (Within)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Edge" => InternedConstructorTemplates.EdgeValue Symbol Guard
local notation "Operations" => SourceEqualityConstraintMemoAllocation.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Prefix" => SourceCurrentAllocatedInheritedPrefix.run
local notation "sourceTop" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)

/-- Both actual returned-field alternatives preserve an original endpoint region. -/
theorem fields_preserve (region : Path → Prop) {symbol : Symbol} {original : Guard} {result : Edge}
    (fields : SourceCurrentOuterRowFieldOrigins.Fields symbol original result)
    (inputs : ∀ path ∈ members ((SourceCompactGuards.sourceEqualities original).getD []), region path) :
    ∀ path ∈ members ((SourceCompactGuards.sourceEqualities result.entry.key.constraint).getD []), region path := by
  rcases fields.2 with same | plain
  · simpa only [same] using inputs
  · intro path member
    rw [plain] at member
    have empty : SourceCompactGuards.sourceEqualities (sourceTop : Guard) = some [] := rfl
    rw [empty] at member
    simp [members] at member

/-- The actual allocated prefix completes with a region-preserving physical value and every raw child suffix region. -/
theorem run_preserves (region : Path → Prop)
    (rightClosed : ∀ path, region path → ∀ suffix, region (path ++ suffix))
    (original : Guard) (inherited : EqValue) (before : Operations)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before)
    (field : SourceCurrentConjunctionEquality.FieldAvailable before original)
    (inheritedReady : EqReady before.constraints inherited)
    (inheritedWithin : Within region inherited.payload)
    (ownEndpoints : ∀ path ∈ members ((SourceCompactGuards.sourceEqualities original).getD []), region path) :
    ∃ combined,
      (Prefix original inherited before).1 = .ok (some combined) ∧
      SourceEqualityConstraintMemoAllocation.Valid (Prefix original inherited before).2 ∧
      EqReady (Prefix original inherited before).2.constraints combined ∧
      SourceEqualityConstraintMemoAllocation.Grows before (Prefix original inherited before).2 ∧
      Within region combined.payload ∧
      ∀ index, Within (fun suffix => region (index :: suffix))
        (SourceEqualityDescend.descend combined.payload index) := by
  cases inherited with
  | contradiction =>
      refine ⟨.contradiction, rfl, valid, inheritedReady,
        SourceEqualityConstraintMemoAllocation.grows_refl before, ?_, ?_⟩
      · trivial
      · intro index
        trivial
  | live identity records =>
      obtain ⟨own, accessorDone, accessorValid, ownReady, _classes, physical, accessorGrows⟩ :=
        SourceCurrentConjunctionEquality.accessor_correct original before valid field
      have ownWithin : Within region own.payload := by
        apply SourceEqualityConstraintRegions.read_preserves region
          (SourceCompactGuards.sourceEqualities original)
          (SourceEqualityGuardReadback.source_cached original field.1) ?_ own.payload physical
        intro classes same path member
        apply ownEndpoints path
        simpa only [same, Option.getD] using member
      obtain ⟨combined, combinedDone, combinedValid, combinedReady, literal, combinedGrows⟩ :=
        SourceEqualityConstraintMemoAllocation.combine_correct (.live identity records) own
          (SourceCurrentConjunctionEquality.accessor original before).2 accessorValid
          (inheritedReady.grows accessorGrows.constraint_growth) ownReady
      have actual : Prefix original (.live identity records) before =
          (.ok (some combined),
            (SourceEqualityConstraintMemoAllocation.combine (.live identity records) own
              (SourceCurrentConjunctionEquality.accessor original before).2).2) := by
        simp only [SourceCurrentAllocatedInheritedPrefix.run_combine original identity records before own accessorDone,
          combinedDone, Except.map]
      have combinedWithin : Within region combined.payload :=
        SourceEqualityConstraintRegions.combine_preserves region rightClosed
          (some records) own.payload combined.payload inheritedWithin ownWithin literal
      refine ⟨combined, congrArg Prod.fst actual, ?_, ?_, ?_, combinedWithin, ?_⟩
      · simpa only [actual] using combinedValid
      · simpa only [actual] using combinedReady
      · simpa only [actual] using SourceCurrentConjunctionEquality.grows_trans accessorGrows combinedGrows
      · exact SourceEqualityConstraintRegions.descend_preserves region combined.payload
          combinedReady.2 combinedWithin

/-- Actual caller descent has the same region as its literal physical trie descent. -/
theorem descend_preserves (region : Path → Prop) {width : Nat}
    (before : Caller width) (combined : EqValue) (index : Nat)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before.checked.operations)
    (ready : EqReady before.checked.operations.constraints combined)
    (within : Within region combined.payload) :
    Within (fun suffix => region (index :: suffix))
      (SourceCurrentAllocatedPartialGraph.descend before combined index).1.payload := by
  have checked := SourceEqualityConstraintMemoAllocation.descend_correct combined index before.checked.operations valid ready
  change Within (fun suffix => region (index :: suffix))
    (SourceEqualityConstraintMemoAllocation.descend combined index before.checked.operations).1.payload
  rw [checked.2.2.1]
  exact SourceEqualityConstraintRegions.descend_preserves region combined.payload ready.2 within index

end MicroCFTA.SourceCurrentInheritedConstraintRegions
