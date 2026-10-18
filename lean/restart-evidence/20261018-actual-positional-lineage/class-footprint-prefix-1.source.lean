import MicroCFTA.SourceCurrentAllocatedClassWorker

/-!
# Literal class edit footprints

Original class paths determine the child positions that the compiler can
visit. An untouched child excludes edits at that child and its ancestors.
Actual successful class returns retain the ordered prefix and selected
call. These laws do not assert outer recursive progress.
-/
namespace MicroCFTA.SourceCurrentClassPositionalFootprints
open InternedConstructorTemplates SourceEqualityEdits SourceEqualityNeededMap
open SourceEqualityEditLeafPaths SourceCurrentEditDomains
open SourceCurrentAllocatedClassEditPlan
local notation "Record" => SourceEqualityClassOrder.Record
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Shared" => SourceCurrentAllocatedSharedTargetState.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard

/-- No source callback is at, above, or below this indexed child. -/
def Unselected (record : Record) (forestIndex childIndex : Nat) : Prop :=
  ∀ path ∈ record.paths, SourceEqualityEditCompiledPaths.Disjoint
    (path.map Int.ofNat) [Int.ofNat forestIndex, Int.ofNat childIndex]

private def Detached (edits : Edits Action) (target : List Int) : Prop :=
  ∀ path action, (path, action) ∈ leaves edits → SourceEqualityEditCompiledPaths.Disjoint path target

private theorem detached_below {edits : Edits Action} {target : List Int}
    (detached : Detached edits target) : ∃ entries, edits = .editBelow entries := by
  cases edits with
  | editAt action =>
      exact False.elim ((detached [] action (by simp [leaves])).1 ⟨target, rfl⟩)
  | editBelow entries => exact ⟨entries,rfl⟩

private theorem detached_child {entries : List (Int × Edits Action)} {index : Int}
    {target : List Int} {child : Edits Action}
    (detached : Detached (.editBelow entries) (index :: target))
    (found : lookup index entries = some child) : Detached child target := by
  intro path action member
  have parent := detached (index :: path) action
    (below_member entries index child (lookup_mem _ _ _ found) path action member)
  exact ⟨fun prefix => parent.1 (List.cons_prefix_cons.mpr ⟨rfl,prefix⟩),
    fun prefix => parent.2 (List.cons_prefix_cons.mpr ⟨rfl,prefix⟩)⟩

private theorem detached_absent {entries : List (Int × Edits Action)} {index : Int}
    (populated : Populated (.editBelow entries))
    (detached : Detached (.editBelow entries) [index]) : lookup index entries = none := by
  cases found : lookup index entries with
  | none => rfl
  | some child =>
      obtain ⟨path,action,member⟩ := (populated index child (lookup_mem _ _ _ found)).2
      have parent := detached (index :: path) action
        (below_member entries index child (lookup_mem _ _ _ found) path action member)
      exact False.elim (parent.2 ⟨path,rfl⟩)

/-- Original path exclusion gives the exact absent compiled child dispatch. -/
theorem compiled_unselected (record : Record) (coherent : SourceEqualityClassOrder.Coherent record)
    (forestIndex childIndex : Nat) (unselected : Unselected record forestIndex childIndex) :
    ∃ entries, compiled record = .editBelow entries ∧
      (lookup (Int.ofNat forestIndex) entries = none ∨
        ∃ children, lookup (Int.ofNat forestIndex) entries = some (.editBelow children) ∧
          lookup (Int.ofNat childIndex) children = none) := by
  have detached : Detached (compiled record) [Int.ofNat forestIndex,Int.ofNat childIndex] := by
    intro path action member
    have original := (SourceEqualityEditCompiledPaths.build_leaves
      (SourceEqualityClassEdits.edits record.paths id) (compiled_disjoint record coherent)).mem_iff.mp member
    obtain ⟨natural,included,same⟩ := List.mem_map.mp original
    cases same
    exact unselected natural included
  obtain ⟨entries,built⟩ := detached_below detached
  refine ⟨entries,built,?_⟩
  rw [built] at detached
  cases found : lookup (Int.ofNat forestIndex) entries with
  | none => exact Or.inl rfl
  | some child =>
      have next := detached_child detached found
      obtain ⟨children,shape⟩ := detached_below next
      have populated := compiled_populated record
      rw [built] at populated
      have childPopulated := (populated _ _ (lookup_mem _ _ _ found)).1
      rw [shape] at next childPopulated
      exact Or.inr ⟨children,by simpa only [shape] using found,detached_absent childPopulated next⟩

end MicroCFTA.SourceCurrentClassPositionalFootprints
