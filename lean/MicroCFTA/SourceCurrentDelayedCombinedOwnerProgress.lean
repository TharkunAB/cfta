import MicroCFTA.SourceCurrentInheritedOwnerProgress

/-!
# Delayed descent from a class in the combined constraint

A class in the actual combined payload can contain a same-child pair
created by normalization. The pair need not occur in one effective own
class. Later literal descent retains a nonempty suffix class and cannot
reuse an initially ready Top owner's node key.
-/
namespace MicroCFTA.SourceCurrentDelayedCombinedOwnerProgress
open EqualityNormalize SourceEqualityClassOrder SourceEqualityConstraintAllocation
local notation "Operations" => SourceEqualityConstraintMemoAllocation.State
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "prefix" => SourceCurrentAllocatedInheritedPrefix.run
local notation "descend" => SourceEqualityConstraintMemoAllocation.descend
local notation "Grows" => SourceEqualityConstraintMemoAllocation.Grows
local notation "Valid" => SourceEqualityConstraintMemoAllocation.Valid

private theorem descend_nonempty (before : Operations) (combined : Value)
    (ready : Ready before.constraints combined) (paths : Class)
    (selected : paths ∈ (SourceEqualityInheritedPayload.classes combined.payload).getD [])
    (index : Nat) (left right : Path) (first : index :: left ∈ paths)
    (second : index :: right ∈ paths) (different : left ≠ right) :
    SourceEqualityDescend.descend combined.payload index ≠ some [] := by
  cases combined with
  | contradiction =>
      change paths ∈ ([] : Constraints) at selected
      cases selected
  | live identity records =>
      change paths ∈ records.map Record.paths at selected
      obtain ⟨record, member, rfl⟩ := List.mem_map.mp selected
      have coherent := (ready.2 records rfl record member).1
      have valid := EqualityTrie.descend_valid record.trie coherent.1 index
      have pairs := EqualityTrie.descend_exact record.trie coherent.1 index
      have kept := (EqualitySaturation.pathTrieHasAtLeastTwoPaths_nontrivial _ valid).mpr
        ⟨left, (pairs left).mpr ((coherent.2.2 _).mpr first),
          right, (pairs right).mpr ((coherent.2.2 _).mpr second), different⟩
      have found : SourceEqualityDescend.record index record =
          some (SourceEqualityDescend.fromTrie (EqualityTrie.pathTrieDescend record.trie index)) := by
        simp only [SourceEqualityDescend.record, kept, ite_true]
      have present := (SourceEqualityDescend.records_perm index records).mem_iff.mpr
        (List.mem_filterMap.mpr ⟨record, member, found⟩)
      have exactPayload : SourceEqualityDescend.descend (some records) index =
          some (SourceEqualityDescend.records index records) := by cases records <;> rfl
      change SourceEqualityDescend.descend (some records) index ≠ some []
      rw [exactPayload]
      intro empty
      exact List.not_mem_nil (Option.some.inj empty ▸ present)

/-- A pair in the actual combined component separates delayed descent from every initial Top owner. -/
theorem key_ne_top (original : Guard) (inherited : Value) (before : Operations)
    (valid : Valid before) (ready : Ready before.constraints inherited)
    (field : SourceCurrentConjunctionEquality.FieldAvailable before original)
    (combined : Value) (actual : (prefix original inherited before).1 = .ok (some combined))
    (later : Operations) (laterValid : Valid later)
    (laterGrowth : Grows (prefix original inherited before).2 later)
    (paths : Class)
    (selected : paths ∈ (SourceEqualityInheritedPayload.classes combined.payload).getD [])
    (index : Nat) (left right : Path) (first : index :: left ∈ paths)
    (second : index :: right ∈ paths) (different : left ≠ right)
    (identity : Nat) (top : Ready before.constraints (.live identity []))
    (value owner : InternedConstructorTemplates.Value (SourceObservations.Label FullSyntax.Formula) Guard) :
    let child := descend combined index later
    Valid child.2 ∧ Ready child.2.constraints child.1 ∧ Grows later child.2 ∧
      Grows before child.2 ∧ child.1.payload ≠ some [] ∧
      (SourceCurrentAllocatedPartialState.NodeRequest.mk child.1 value).key ≠
        (SourceCurrentAllocatedPartialState.NodeRequest.mk (.live identity []) owner).key := by
  obtain ⟨chosen, computed, _, combinedReady, prefixGrowth, _⟩ :=
    SourceCurrentEqualityOperationFixed.inherited_prefix original inherited before valid ready field
  have same : chosen = combined := Option.some.inj (Except.ok.inj (computed.symm.trans actual))
  subst chosen
  have currentReady := combinedReady.grows laterGrowth.constraint_growth
  have checked := SourceEqualityConstraintMemoAllocation.descend_correct combined index later laterValid currentReady
  have nonempty : (descend combined index later).1.payload ≠ some [] := by
    rw [checked.2.2.1]
    exact descend_nonempty later combined currentReady paths selected index left right first second different
  have totalGrowth := SourceCurrentConjunctionEquality.grows_trans prefixGrowth
    (SourceCurrentConjunctionEquality.grows_trans laterGrowth checked.2.2.2)
  exact ⟨checked.1, checked.2.1, checked.2.2.2, totalGrowth, nonempty,
    SourceCurrentInheritedOwnerProgress.node_key_ne_top before _ checked.1 totalGrowth
      _ checked.2.1 nonempty identity top value owner⟩

end MicroCFTA.SourceCurrentDelayedCombinedOwnerProgress
