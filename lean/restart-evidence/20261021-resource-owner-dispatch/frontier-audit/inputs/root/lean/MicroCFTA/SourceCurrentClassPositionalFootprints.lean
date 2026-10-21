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
  exact ⟨fun initial => parent.1 (List.cons_prefix_cons.mpr ⟨rfl,initial⟩),
    fun initial => parent.2 (List.cons_prefix_cons.mpr ⟨rfl,initial⟩)⟩

private theorem detached_absent {entries : List (Int × Edits Action)} {index : Int}
    (populated : Populated (.editBelow entries))
    (detached : Detached (.editBelow entries) [index]) : lookup index entries = none := by
  cases found : lookup index entries with
  | none => rfl
  | some child =>
      rw [Populated] at populated
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
      rw [built,Populated] at populated
      have childPopulated := (populated _ _ (lookup_mem _ _ _ found)).1
      rw [shape] at next childPopulated
      exact Or.inr ⟨children,by rw [← shape],detached_absent childPopulated next⟩


open SourceCurrentAllocatedSharedEditWorker

private theorem bind_done (first : Outcome width A)
    (next : A → Shared width → Outcome width B) {value : B} {after : Shared width}
    (actual : first.bind next = .done value after) :
    ∃ result middle, first = .done result middle ∧ next result middle = .done value after := by
  cases first with
  | done result middle => exact ⟨result,middle,rfl,actual⟩
  | failed => cases actual

private theorem children_slice
    (recur : Edits EqualityNormalize.Path → Value Symbol Guard → Shared width → Outcome width (Value Symbol Guard))
    (entries : List (Int × Edits EqualityNormalize.Path))
    {offset : Nat} {values results : List (Value Symbol Guard)} {before after : Shared width}
    (actual : children recur entries offset values before = .done results after)
    {index : Nat} {result : Value Symbol Guard} (selected : results[index]? = some result) :
    ∃ original start finish,
      values[index]? = some original ∧
      children recur entries offset (values.take index) before = .done (results.take index) start ∧
      children recur entries (offset + index + 1) (values.drop (index + 1)) finish =
        .done (results.drop (index + 1)) after ∧
      ((lookup ((offset + index : Nat) : Int) entries = none ∧ result = original ∧ finish = start) ∨
        ∃ edits, lookup ((offset + index : Nat) : Int) entries = some edits ∧
          recur edits original start = .done result finish) := by
  induction values generalizing offset results before after index result with
  | nil => simp only [children] at actual; cases actual; simp at selected
  | cons value values ih =>
      cases found : lookup (offset : Int) entries with
      | none =>
          simp only [children,found] at actual
          obtain ⟨tail,last,rest,done⟩ := bind_done _ _ actual
          cases done
          cases index with
          | zero =>
              have same : value = result := by simpa using selected
              subst result
              exact ⟨value,before,before,rfl,rfl,by simpa using rest,Or.inl ⟨by simpa using found,rfl,rfl⟩⟩
          | succ index =>
              obtain ⟨original,start,finish,source,first,last,dispatch⟩ := ih rest (by simpa using selected)
              refine ⟨original,start,finish,by simpa using source,?_,?_,?_⟩
              · simp only [List.take_succ_cons,children,found,first,Outcome.bind]
              · simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using last
              · simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using dispatch
      | some edits =>
          simp only [children,found] at actual
          obtain ⟨output,middle,first,rest⟩ := bind_done _ _ actual
          obtain ⟨tail,last,rest,done⟩ := bind_done _ _ rest
          cases done
          cases index with
          | zero =>
              have same : output = result := by simpa using selected
              subst result
              exact ⟨value,before,middle,rfl,rfl,by simpa using rest,Or.inr ⟨edits,by simpa using found,first⟩⟩
          | succ index =>
              obtain ⟨original,start,finish,source,earlier,later,dispatch⟩ := ih rest (by simpa using selected)
              refine ⟨original,start,finish,by simpa using source,?_,?_,?_⟩
              · simp only [List.take_succ_cons,children,found,first,Outcome.bind,earlier]
              · simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using later
              · simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using dispatch

/-- A literal class return retains the actual earlier and later child schedule. -/
theorem class_dispatch [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {e p h m s n : Nat} {record : Record} {values results : List (Value Symbol Guard)}
    {before after : Checked width} {memo saved : Memo}
    (actual : SourceCurrentAllocatedClassWorker.runClass e p h m s n record values before memo =
      .done results after saved)
    (coherent : SourceEqualityClassOrder.Coherent record)
    (forestIndex childIndex : Nat) (unselected : Unselected record forestIndex childIndex)
    {result : Value Symbol Guard} (selected : results[forestIndex]? = some result) :
    ∃ entries, ∃ shared start finish : Shared width, ∃ original,
      compiled record = .editBelow entries ∧ shared.checked = after ∧ shared.memo = saved ∧
      values[forestIndex]? = some original ∧
      children (edit record values e p h m s n) entries 0 (values.take forestIndex)
        (SourceCurrentAllocatedSharedTargetState.initial before memo) = .done (results.take forestIndex) start ∧
      children (edit record values e p h m s n) entries (forestIndex + 1)
        (values.drop (forestIndex + 1)) finish = .done (results.drop (forestIndex + 1)) shared ∧
      ((lookup (Int.ofNat forestIndex) entries = none ∧ result = original ∧ finish = start) ∨
        ∃ childEntries, lookup (Int.ofNat forestIndex) entries = some (.editBelow childEntries) ∧
          lookup (Int.ofNat childIndex) childEntries = none ∧
          edit record values e p h m s n (.editBelow childEntries) original start = .done result finish) := by
  obtain ⟨entries,built,footprint⟩ := compiled_unselected record coherent forestIndex childIndex unselected
  unfold SourceCurrentAllocatedClassWorker.runClass at actual
  cases executed : editList (edit record values e p h m s n) (compiled record) values
      (SourceCurrentAllocatedSharedTargetState.initial before memo) with
  | failed => simp only [executed] at actual; cases actual
  | done output shared =>
      simp only [executed] at actual
      cases actual
      rw [built,editList] at executed
      obtain ⟨original,start,finish,source,earlier,later,dispatch⟩ := children_slice _ _ executed selected
      refine ⟨entries,shared,start,finish,original,built,rfl,rfl,source,earlier,by simpa using later,?_⟩
      rcases dispatch with absent | ⟨edits,found,done⟩
      · exact Or.inl ⟨by simpa using absent.1,absent.2⟩
      · rcases footprint with absent | ⟨childEntries,matched,unselected⟩
        · have found' : lookup (Int.ofNat forestIndex) entries = some edits := by
            simpa only [Nat.zero_add,Int.ofNat_eq_natCast] using found
          rw [absent] at found'
          cases found'
        · have same : edits = .editBelow childEntries := Option.some.inj
            ((by simpa using found : lookup (Int.ofNat forestIndex) entries = some edits).symm.trans matched)
          subst edits
          exact Or.inr ⟨childEntries,matched,unselected,done⟩

end MicroCFTA.SourceCurrentClassPositionalFootprints
