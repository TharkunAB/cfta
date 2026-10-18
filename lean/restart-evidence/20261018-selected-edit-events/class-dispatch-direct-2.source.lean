import MicroCFTA.SourceCurrentClassPositionalFootprints

/-!
# Actual class dispatch at every selected child

Compiled leaves retain their complete original natural path. The literal
child worker supplies exact earlier and later calls at every returned slot.
A coherent active class either retains the slot, executes its whole-slot
leaf, or edits below it. No unselected footprint, future row law or semantic
read receipt is supplied. Successful worker equations remain explicit.
-/
namespace MicroCFTA.SourceCurrentActualClassDispatch
open InternedConstructorTemplates SourceEqualityEdits SourceEqualityNeededMap
open SourceEqualityEditLeafPaths SourceCurrentAllocatedClassEditPlan
open SourceCurrentAllocatedSharedEditWorker
local notation "Record" => SourceEqualityClassOrder.Record
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Shared" => SourceCurrentAllocatedSharedTargetState.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard

/-- A compiled callback retains its exact complete natural source path. -/
theorem compiled_leaf (record : Record) (coherent : SourceEqualityClassOrder.Coherent record)
    {path : Path} {target : EqualityNormalize.Path}
    (member : (path,target) ∈ leaves (compiled record)) :
    target ∈ record.paths ∧ path = target.map Int.ofNat := by
  have original := (SourceEqualityEditCompiledPaths.build_leaves
    (SourceEqualityClassEdits.edits record.paths id) (compiled_disjoint record coherent)).mem_iff.mp member
  obtain ⟨natural,included,same⟩ := List.mem_map.mp original
  cases same
  exact ⟨included,rfl⟩

private theorem bind_done (first : Outcome width A)
    (next : A → Shared width → Outcome width B) {value : B} {after : Shared width}
    (actual : first.bind next = .done value after) :
    ∃ result middle, first = .done result middle ∧ next result middle = .done value after := by
  cases first with
  | done result middle => exact ⟨result,middle,rfl,actual⟩
  | failed => cases actual

/-- Every present returned slot retains the literal earlier and later child schedule. -/
theorem children_indexed
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

/-- Every actual active class slot is unchanged, replaced by its literal leaf call, or edited below. -/
theorem class_dispatch [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {e p h m s n : Nat} {record : Record} {values results : List Node}
    {before after : Checked width} {memo saved : Memo}
    (actual : SourceCurrentAllocatedClassWorker.runClass e p h m s n record values before memo =
      .done results after saved)
    (coherent : SourceEqualityClassOrder.Coherent record)
    (active : EqualityNormalize.Nontrivial record.paths)
    (forestIndex : Nat) {result : Node} (selected : results[forestIndex]? = some result) :
    ∃ entries, ∃ shared start finish : Shared width, ∃ original,
      compiled record = .editBelow entries ∧ shared.checked = after ∧ shared.memo = saved ∧
      values[forestIndex]? = some original ∧
      children (edit record values e p h m s n) entries 0 (values.take forestIndex)
        (SourceCurrentAllocatedSharedTargetState.initial before memo) = .done (results.take forestIndex) start ∧
      children (edit record values e p h m s n) entries (forestIndex + 1)
        (values.drop (forestIndex + 1)) finish = .done (results.drop (forestIndex + 1)) shared ∧
      ((lookup (Int.ofNat forestIndex) entries = none ∧ result = original ∧ finish = start) ∨
        (lookup (Int.ofNat forestIndex) entries = some (.editAt [forestIndex]) ∧
          [forestIndex] ∈ record.paths ∧ 0 < e ∧
          leaf p h m s n record values [forestIndex] original start = .done result finish) ∨
        (∃ childEntries, lookup (Int.ofNat forestIndex) entries = some (.editBelow childEntries) ∧
          0 < e ∧ edit record values e p h m s n (.editBelow childEntries) original start = .done result finish)) := by
  obtain ⟨entries,built⟩ := compiled_children record coherent active
  unfold SourceCurrentAllocatedClassWorker.runClass at actual
  cases executed : editList (edit record values e p h m s n) (compiled record) values
      (SourceCurrentAllocatedSharedTargetState.initial before memo) with
  | failed => simp only [executed] at actual; cases actual
  | done output shared =>
    simp only [executed] at actual
    cases actual
    rw [built,editList] at executed
    obtain ⟨original,start,finish,source,earlier,later,dispatch⟩ := children_indexed _ _ executed selected
    refine ⟨entries,shared,start,finish,original,built,rfl,rfl,source,earlier,by simpa using later,?_⟩
    rcases dispatch with absent | ⟨edits,found,done⟩
    · exact Or.inl ⟨by simpa using absent.1,absent.2⟩
    · have found : lookup (Int.ofNat forestIndex) entries = some edits := by simpa using found
      cases edits with
      | editAt target =>
        have member : ([Int.ofNat forestIndex],target) ∈ leaves (compiled record) := by
          rw [built]
          exact below_member entries _ _ (lookup_mem _ _ _ found) [] target (by simp [leaves])
        have originalPath := compiled_leaf record coherent member
        have token : target = [forestIndex] := by
          have decoded := congrArg (List.map Int.toNat) originalPath.2
          simp only [List.map_map,Function.comp_def] at decoded
          change [forestIndex] = target.map id at decoded
          simpa only [List.map_id] using decoded.symm
        subst target
        cases e with
        | zero => simp only [edit] at done; cases done
        | succ e => exact Or.inr (Or.inl ⟨found,originalPath.1,Nat.zero_lt_succ _,done⟩)
      | editBelow childEntries =>
        cases e with
        | zero => simp only [edit] at done; cases done
        | succ e => exact Or.inr (Or.inr ⟨childEntries,found,Nat.zero_lt_succ _,done⟩)

end MicroCFTA.SourceCurrentActualClassDispatch
