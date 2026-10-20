import MicroCFTA.SourceCurrentInheritedOwnerProgress

/-!
# Nonempty inherited constraints after delayed descent

A same-child pair in an effective own class survives the actual prefix.
Later operation growth retains the combined constraint. Literal descent
at that later state has the same payload as immediate descent. Its node
key differs from every initially ready Top owner's key.
-/
namespace MicroCFTA.SourceCurrentDelayedOwnerProgress
open EqualityNormalize SourceEqualityClassOrder SourceEqualityConstraintAllocation
local notation "Operations" => SourceEqualityConstraintMemoAllocation.State
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "prefix" => SourceCurrentAllocatedInheritedPrefix.run
local notation "descend" => SourceEqualityConstraintMemoAllocation.descend
local notation "Grows" => SourceEqualityConstraintMemoAllocation.Grows
local notation "Valid" => SourceEqualityConstraintMemoAllocation.Valid

/-- A retained same-child pair constrains the same literal descent after later operation growth. -/
theorem selected_split (original : Guard) (inherited : Value) (before : Operations)
    (valid : Valid before) (ready : Ready before.constraints inherited)
    (field : SourceCurrentConjunctionEquality.FieldAvailable before original)
    (combined : Value) (actual : (prefix original inherited before).1 = .ok (some combined))
    (later : Operations) (laterValid : Valid later)
    (laterGrowth : Grows (prefix original inherited before).2 later)
    (paths : Class) (selected : paths ∈ (SourceCompactGuards.sourceEqualities original).getD [])
    (index : Nat) (left right : Path) (first : index :: left ∈ paths)
    (second : index :: right ∈ paths) (different : left ≠ right) :
    let child := descend combined index later
    Valid child.2 ∧ Ready child.2.constraints child.1 ∧ Grows later child.2 ∧
      Grows before child.2 ∧ child.1.payload ≠ some [] := by
  obtain ⟨chosen, computed, middleValid, combinedReady, prefixGrowth, _, _, _, nonempty⟩ :=
    SourceCurrentInheritedOwnerProgress.selected_split original inherited before valid ready field
      paths selected index left right first second different
  have same : chosen = combined := Option.some.inj (Except.ok.inj (computed.symm.trans actual))
  subst chosen
  have immediate := SourceEqualityConstraintMemoAllocation.descend_correct combined index
    (prefix original inherited before).2 middleValid combinedReady
  have current := SourceEqualityConstraintMemoAllocation.descend_correct combined index later laterValid
    (combinedReady.grows laterGrowth.constraint_growth)
  refine ⟨current.1, current.2.1, current.2.2.2,
    SourceCurrentConjunctionEquality.grows_trans prefixGrowth
      (SourceCurrentConjunctionEquality.grows_trans laterGrowth current.2.2.2), ?_⟩
  intro empty
  exact nonempty (immediate.2.2.1.trans (current.2.2.1.symm.trans empty))

/-- The delayed child cannot share the key of any initially ready Top owner. -/
theorem key_ne_top (original : Guard) (inherited : Value) (before : Operations)
    (valid : Valid before) (ready : Ready before.constraints inherited)
    (field : SourceCurrentConjunctionEquality.FieldAvailable before original)
    (combined : Value) (actual : (prefix original inherited before).1 = .ok (some combined))
    (later : Operations) (laterValid : Valid later)
    (laterGrowth : Grows (prefix original inherited before).2 later)
    (paths : Class) (selected : paths ∈ (SourceCompactGuards.sourceEqualities original).getD [])
    (index : Nat) (left right : Path) (first : index :: left ∈ paths)
    (second : index :: right ∈ paths) (different : left ≠ right)
    (identity : Nat) (top : Ready before.constraints (.live identity []))
    (value owner : InternedConstructorTemplates.Value (SourceObservations.Label FullSyntax.Formula) Guard) :
    let child := descend combined index later
    (SourceCurrentAllocatedPartialState.NodeRequest.mk child.1 value).key ≠
      (SourceCurrentAllocatedPartialState.NodeRequest.mk (.live identity []) owner).key := by
  obtain ⟨childValid, childReady, _, totalGrowth, nonempty⟩ :=
    selected_split original inherited before valid ready field combined actual later laterValid laterGrowth
      paths selected index left right first second different
  exact SourceCurrentInheritedOwnerProgress.node_key_ne_top before _ childValid totalGrowth
    _ childReady nonempty identity top value owner

end MicroCFTA.SourceCurrentDelayedOwnerProgress
