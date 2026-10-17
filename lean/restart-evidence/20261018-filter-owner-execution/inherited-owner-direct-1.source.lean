import MicroCFTA.SourceCurrentOuterOriginDependencies

/-!
# A retained local equality separates a child from Top owners

Two distinct paths in one effective own class can enter the same child.
Actual inherited-first combination retains both paths in one component.
Actual trie descent therefore returns a nonempty payload or contradiction.
Its allocated key differs from every initially ready empty inherited value.
This result does not cover classes whose paths enter different children.
-/
namespace MicroCFTA.SourceCurrentInheritedOwnerProgress
open EqualityNormalize SourceEqualityClassOrder SourceEqualityConstraintAllocation
local notation "Operations" => SourceEqualityConstraintMemoAllocation.State
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "prefix" => SourceCurrentAllocatedInheritedPrefix.run

private theorem retained (index : Nat) (original : Record) (coherent : Coherent original)
    (left right : Path) (first : index :: left ∈ original.paths)
    (second : index :: right ∈ original.paths) (different : left ≠ right) :
    ∃ output, SourceEqualityDescend.record index original = some output := by
  have valid := EqualityTrie.descend_valid original.trie coherent.1 index
  have pairs := EqualityTrie.descend_exact original.trie coherent.1 index
  have kept := (EqualitySaturation.pathTrieHasAtLeastTwoPaths_nontrivial _ valid).mpr
    ⟨left, (pairs left).mpr ((coherent.2.2 _).mpr first),
      right, (pairs right).mpr ((coherent.2.2 _).mpr second), different⟩
  exact ⟨SourceEqualityDescend.fromTrie (EqualityTrie.pathTrieDescend original.trie index),
    by simp only [SourceEqualityDescend.record, kept, ite_true]⟩

private theorem covered_nonempty (input : Constraints) (combined : Value)
    (ready : Ready before.constraints combined)
    (covered : ∀ outputs, combined.payload = some outputs → Covers input (outputs.map Record.paths))
    (paths : Class) (selected : paths ∈ input) (index : Nat) (left right : Path)
    (first : index :: left ∈ paths) (second : index :: right ∈ paths) (different : left ≠ right)
    (payload : child.payload = SourceEqualityDescend.descend combined.payload index) :
    child.payload ≠ some [] := by
  cases combined with
  | contradiction => simpa only [Value.payload, SourceEqualityDescend.descend] using payload
  | live identity outputs =>
      obtain ⟨component, member, includes⟩ := covered outputs rfl paths selected
      obtain ⟨original, included, same⟩ := List.mem_map.mp member
      subst component
      obtain ⟨output, actual⟩ := retained index original (ready.2 outputs rfl original included).1
        left right (includes _ first) (includes _ second) different
      have present : output ∈ SourceEqualityDescend.records index outputs :=
        (SourceEqualityDescend.records_perm index outputs).mem_iff.mpr
          (List.mem_filterMap.mpr ⟨original, included, actual⟩)
      have nonempty : outputs ≠ [] := List.ne_nil_of_mem included
      have exactPayload : child.payload = some (SourceEqualityDescend.records index outputs) := by
        cases outputs with
        | nil => exact False.elim (nonempty rfl)
        | cons head rest => exact payload
      intro empty
      have absent := Option.some.inj (exactPayload.symm.trans empty)
      exact List.not_mem_nil (absent ▸ present)

/-- Initial effective own paths construct a nonempty actual child constraint. -/
theorem selected_split (original : Guard) (inherited : Value) (before : Operations)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before)
    (ready : Ready before.constraints inherited)
    (field : SourceCurrentConjunctionEquality.FieldAvailable before original)
    (paths : Class) (selected : paths ∈ (SourceCompactGuards.sourceEqualities original).getD [])
    (index : Nat) (left right : Path) (first : index :: left ∈ paths)
    (second : index :: right ∈ paths) (different : left ≠ right) :
    ∃ combined,
      (prefix original inherited before).1 = .ok (some combined) ∧
      let middle := (prefix original inherited before).2
      SourceEqualityConstraintMemoAllocation.Valid middle ∧ Ready middle.constraints combined ∧
      SourceEqualityConstraintMemoAllocation.Grows before middle ∧
      let child := SourceEqualityConstraintMemoAllocation.descend combined index middle
      SourceEqualityConstraintMemoAllocation.Valid child.2 ∧ Ready child.2.constraints child.1 ∧
      SourceEqualityConstraintMemoAllocation.Grows middle child.2 ∧ child.1.payload ≠ some [] := by
  cases inherited with
  | contradiction =>
      have checked := SourceEqualityConstraintMemoAllocation.descend_correct .contradiction index before valid ready
      refine ⟨.contradiction, rfl, valid, ready,
        SourceEqualityConstraintMemoAllocation.grows_refl before,
        checked.1, checked.2.1, checked.2.2.2, ?_⟩
      rw [checked.2.2.1]
      simp only [Value.payload, SourceEqualityDescend.descend, ne_eq, reduceCtorEq, not_false_eq_true]
  | live identity records =>
      obtain ⟨own, loaded, accessorValid, ownReady, classes, _, accessorGrowth⟩ :=
        SourceCurrentConjunctionEquality.accessor_correct original before valid field
      obtain ⟨combined, actual, combinedValid, combinedReady, combineGrowth, _, covered⟩ :=
        SourceCurrentOuterOriginDependencies.combine_covers (.live identity records) own
          (SourceCurrentConjunctionEquality.accessor original before).2 accessorValid
          (ready.grows accessorGrowth.constraint_growth) ownReady
      have computed : prefix original (.live identity records) before =
          (.ok (some combined),
            (SourceEqualityConstraintMemoAllocation.combine (.live identity records) own
              (SourceCurrentConjunctionEquality.accessor original before).2).2) := by
        rw [SourceCurrentAllocatedInheritedPrefix.run_combine original identity records before own loaded]
        simp only [actual, Except.map]
      have checked := SourceEqualityConstraintMemoAllocation.descend_correct combined index _ combinedValid combinedReady
      have member : paths ∈ (SourceEqualityInheritedPayload.classes (.live identity records : Value).payload).getD [] ++
          (SourceEqualityInheritedPayload.classes own.payload).getD [] := by
        exact List.mem_append_right _ (classes ▸ selected)
      refine ⟨combined, congrArg Prod.fst computed, ?_⟩
      simp only [computed]
      exact ⟨combinedValid, combinedReady,
        SourceCurrentConjunctionEquality.grows_trans accessorGrowth combineGrowth,
        checked.1, checked.2.1, checked.2.2.2,
        covered_nonempty _ combined combinedReady covered paths member index left right
          first second different checked.2.2.1⟩

/-- A nonempty dispatched inherited payload cannot share an initially ready Top owner's node key. -/
theorem node_key_ne_top (before after : Operations)
    (valid : SourceEqualityConstraintMemoAllocation.Valid after)
    (growth : SourceEqualityConstraintMemoAllocation.Grows before after)
    (child : Value) (ready : Ready after.constraints child) (nonempty : child.payload ≠ some [])
    (identity : Nat) (top : Ready before.constraints (.live identity []))
    (value owner : InternedConstructorTemplates.Value (SourceObservations.Label FullSyntax.Formula)
      (SourceSymbolicIndex.Constraint FullSyntax.Formula)) :
    (SourceCurrentAllocatedPartialState.NodeRequest.mk child value).key ≠
      (SourceCurrentAllocatedPartialState.NodeRequest.mk (.live identity []) owner).key := by
  intro same
  have inherited := SourceEqualityConstraintMemoAllocation.ready_eq_of_identity after.constraints valid.constraints
    child (.live identity []) ready (top.grows growth.constraint_growth) (congrArg Prod.fst same)
  exact nonempty (congrArg Value.payload inherited)

end MicroCFTA.SourceCurrentInheritedOwnerProgress
