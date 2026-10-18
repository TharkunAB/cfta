import MicroCFTA.SourceCurrentActualClassRowOrigins
import MicroCFTA.SourceCurrentSelectedRootOrigins
import MicroCFTA.SourceCurrentRequiredPathFootprints
import MicroCFTA.SourceCurrentParentGuardHeapReturns

/-!
# Indexed row origins through actual local class reduction

Actual Scan returns supply the selected original root condition. Source
path footprints supply Required compiler absence. Untouched slots retain
their literal value without a recursive plainness condition. Successful
worker equations remain inputs. This module does not prove completion.
-/
namespace MicroCFTA.SourceCurrentActualLocalRowOrigins
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values)
open SourceCurrentActualRequiredRowOrigins (Root Link)
open SourceCurrentClassPositionalFootprints (Unselected)
open SourceCurrentLowerOperationInvariants (Effect)
open SourceCurrentNativeOperationHeap (Good)
open SourceCurrentMemoMergeEffects (Stored)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Record" => SourceEqualityClassOrder.Record
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "GuardHeap" => SourceCurrentConstrainedCapGuardHeap.Heap Plain
variable {width : Nat}

private theorem local_bind_done {A B : Type}
    (first : SourceCurrentAllocatedLocalWorker.Outcome A width)
    (next : A → Checked width → Fourth → Memo → SourceCurrentAllocatedLocalWorker.Outcome B width)
    {value : B} {after : Checked width} {saved : Fourth} {current : Memo}
    (actual : first.bind next = .done value after saved current) :
    ∃ result middle fourth memo, first = .done result middle fourth memo ∧
      next result middle fourth memo = .done value after saved current := by
  cases first with
  | done result middle fourth memo => exact ⟨result,middle,fourth,memo,rfl,actual⟩
  | failed => cases actual

private theorem class_bind_done
    (first : SourceCurrentAllocatedClassWorker.Outcome width)
    (next : List Node → Checked width → Memo → SourceCurrentAllocatedClassWorker.Outcome width)
    {results after saved} (actual : first.bind next = .done results after saved) :
    ∃ values middle memo, first = .done values middle memo ∧ next values middle memo = .done results after saved := by
  cases first with
  | done values middle memo => exact ⟨values,middle,memo,rfl,actual⟩
  | failed => cases actual

private theorem compiled_absent (record : Record) (coherent : SourceEqualityClassOrder.Coherent record)
    (index childIndex : Nat) (unselected : Unselected record index childIndex)
    (untouched : ∀ path ∈ record.paths, ¬ [Int.ofNat index].IsPrefix (path.map Int.ofNat)) :
    ∃ entries, SourceCurrentAllocatedClassEditPlan.compiled record = .editBelow entries ∧
      SourceEqualityNeededMap.lookup (index : Int) entries = none := by
  obtain ⟨entries,built,_⟩ := SourceCurrentClassPositionalFootprints.compiled_unselected record coherent index childIndex unselected
  refine ⟨entries,built,?_⟩
  cases found : SourceEqualityNeededMap.lookup (index : Int) entries with
  | none => rfl
  | some child =>
    have populated := SourceCurrentAllocatedClassEditPlan.compiled_populated record
    rw [built,SourceCurrentEditDomains.Populated] at populated
    obtain ⟨suffix,action,leaf⟩ := (populated _ _ (SourceEqualityNeededMap.lookup_mem _ _ _ found)).2
    have parent := SourceEqualityEditLeafPaths.below_member entries (index : Int) child
      (SourceEqualityNeededMap.lookup_mem _ _ _ found) suffix action leaf
    rw [← built] at parent
    have original := (SourceEqualityEditCompiledPaths.build_leaves _
      (SourceCurrentAllocatedClassEditPlan.compiled_disjoint record coherent)).mem_iff.mp parent
    obtain ⟨path,member,same⟩ := List.mem_map.mp original
    have samePath := congrArg Prod.fst same
    exact False.elim (untouched path member ⟨suffix,by simpa only [List.singleton_append,Int.ofNat_eq_natCast] using samePath.symm⟩)

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem untouched_class {e p h m s n record values before memo results after saved}
    (actual : SourceCurrentAllocatedClassWorker.runClass (width := width) e p h m s n record values before memo = .done results after saved)
    (coherent : SourceEqualityClassOrder.Coherent record) (index childIndex : Nat)
    (unselected : Unselected record index childIndex)
    (untouched : ∀ path ∈ record.paths, ¬ [Int.ofNat index].IsPrefix (path.map Int.ofNat))
    {source result : Node} (input : values[index]? = some source) (output : results[index]? = some result) : result = source := by
  obtain ⟨entries,built,absent⟩ := compiled_absent record coherent index childIndex unselected untouched
  obtain ⟨other,shared,start,finish,original,constructed,sameState,sameMemo,found,earlier,later,dispatch⟩ :=
    SourceCurrentClassPositionalFootprints.class_dispatch actual coherent index childIndex unselected output
  have sameEntries := SourceEqualityEdits.Edits.editBelow.inj (built.symm.trans constructed)
  subst other
  have same : original = source := Option.some.inj (found.symm.trans input)
  subst original
  rcases dispatch with unchanged | ⟨children,selected,_,_⟩
  · exact unchanged.2.1
  · simp only [Int.ofNat_eq_natCast,absent] at selected
    cases selected

/-- An actual class fold leaves a slot outside every retained class path unchanged. -/
theorem untouched_fold {e p h m s n records values before memo results after saved}
    (actual : SourceCurrentAllocatedClassWorker.fold (width := width) e p h m s n records values before memo = .done results after saved)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record) (index childIndex : Nat)
    (unselected : ∀ record ∈ records, Unselected record index childIndex)
    (untouched : ∀ record ∈ records, ∀ path ∈ record.paths, ¬ [Int.ofNat index].IsPrefix (path.map Int.ofNat))
    {source result : Node} (input : values[index]? = some source) (output : results[index]? = some result) : result = source := by
  induction records generalizing values before memo results after saved source result with
  | nil =>
    simp only [SourceCurrentAllocatedClassWorker.fold] at actual
    cases actual
    exact Option.some.inj (output.symm.trans input)
  | cons record records ih =>
    obtain ⟨middle,checked,current,first,last⟩ := class_bind_done _ _ (by simpa only [SourceCurrentAllocatedClassWorker.fold] using actual)
    obtain ⟨entries,shared,start,finish,original,built,sameState,sameMemo,found,earlier,later,dispatch⟩ :=
      SourceCurrentClassPositionalFootprints.class_dispatch last (coherent record List.mem_cons_self) index childIndex
        (unselected record List.mem_cons_self) output
    have tail := ih first (fun record member => coherent record (List.mem_cons_of_mem _ member))
      (fun record member => unselected record (List.mem_cons_of_mem _ member))
      (fun record member => untouched record (List.mem_cons_of_mem _ member)) input found
    exact (untouched_class last (coherent record List.mem_cons_self) index childIndex
      (unselected record List.mem_cons_self) (untouched record List.mem_cons_self) found output).trans tail

/-- Final Empty propagation erases an untouched slot or retains its exact original value. -/
theorem untouched_pass {e p h m s n records values before memo results after saved}
    (actual : SourceCurrentAllocatedClassWorker.pass (width := width) e p h m s n records values before memo = .done results after saved)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record) (index childIndex : Nat)
    (unselected : ∀ record ∈ records, Unselected record index childIndex)
    (untouched : ∀ record ∈ records, ∀ path ∈ record.paths, ¬ [Int.ofNat index].IsPrefix (path.map Int.ofNat))
    {source result : Node} (input : values[index]? = some source) (output : results[index]? = some result) :
    result = .empty ∨ result = source := by
  obtain ⟨middle,checked,current,first,last⟩ := class_bind_done _ _ (by simpa only [SourceCurrentAllocatedClassWorker.pass] using actual)
  cases last
  by_cases erased : middle.any (fun value => value.referenceOf == .empty) = true
  · have member : result ∈ middle.map (fun _ => (Value.empty : Node)) := by
      simpa only [EqualityLeafProjectionRuntimeEmpty.propagate,erased,ite_true,EqualityLeafProjectionRuntimeEmpty.erase]
        using List.mem_of_getElem? output
    obtain ⟨original,included,same⟩ := List.mem_map.mp member
    exact Or.inl same.symm
  · have same : EqualityLeafProjectionRuntimeEmpty.propagate middle = middle := by
      simp [EqualityLeafProjectionRuntimeEmpty.propagate,erased]
    exact Or.inr (untouched_fold first coherent index childIndex unselected untouched input (by simpa only [same] using output))

variable [DecidableEq Node]

/-- Actual local class reduction derives row origins without a supplied recursive root condition. -/
theorem classes {g s r e p h m c n budget records values before fourth memo results after saved current}
    (actual : SourceCurrentAllocatedLocalWorker.classes g s r e p h m c n budget records values before fourth memo = .done results after saved current)
    (good : Good (width := width) before) (stored : Stored before.native.machine.heap memo)
    (available : Values before.native.machine.heap values) (guards : GuardHeap before.native.machine.heap)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record) (index childIndex : Nat)
    (unselected : ∀ record ∈ records, Unselected record index childIndex)
    {source result : Node} (input : values[index]? = some source) (output : results[index]? = some result) :
    Link childIndex source result := by
  cases scanCall : SourceCurrentAllocatedRecordScanWorker.scan g s p h n budget values records before fourth with
  | failed =>
    simp only [SourceCurrentAllocatedLocalWorker.classes,SourceCurrentAllocatedLocalWorker.scan,scanCall,
      SourceCurrentAllocatedLocalWorker.Outcome.bind] at actual
    cases actual
  | done selected checked scanned =>
    have later := actual
    simp only [SourceCurrentAllocatedLocalWorker.classes,SourceCurrentAllocatedLocalWorker.scan,scanCall,
      SourceCurrentAllocatedLocalWorker.Outcome.bind] at later
    cases selected with
    | mk stopped kept =>
      cases stopped with
      | some paths =>
        simp only at later
        cases later
        have member : result ∈ values.map (fun _ => (Value.empty : Node)) := List.mem_of_getElem? output
        obtain ⟨original,included,same⟩ := List.mem_map.mp member
        cases same
        intro row impossible
        cases impossible
      | none =>
        simp only at later
        have projected : SourceCurrentAllocatedScanWorker.scan g s p h n budget values
            (records.map SourceEqualityClassOrder.Record.paths) before fourth =
            .done (none,kept.map SourceEqualityClassOrder.Record.paths) checked scanned := by
          rw [← SourceCurrentAllocatedRecordScanWorker.scan_mapPaths,scanCall]
          rfl
        have effect := SourceCurrentParentOperationInvariants.scan projected good available
        have heap := SourceCurrentParentGuardHeapReturns.scan Plain projected good available guards
        have keptCoherent : ∀ record ∈ kept, SourceEqualityClassOrder.Coherent record := fun record member =>
          coherent record (SourceCurrentSelectedRootOrigins.selected_primary scanCall member).1
        have keptUnselected : ∀ record ∈ kept, Unselected record index childIndex := fun record member =>
          unselected record (SourceCurrentSelectedRootOrigins.selected_primary scanCall member).1
        obtain ⟨prepared,preparedBefore,next,warm,requiredDone,passDone⟩ := local_bind_done _ _ later
        cases requiredCall : SourceEqualityRequiredExecution.requireAll r h
            (SourceEqualitySelectedRequired.paths (kept.map SourceEqualityClassOrder.Record.paths)) values checked.native.machine.heap with
        | pending | unresolved | exhausted =>
          simp only [SourceCurrentAllocatedLocalWorker.required,requiredCall] at requiredDone
          cases requiredDone
        | done preparedValues preparedHeap =>
          simp only [SourceCurrentAllocatedLocalWorker.required,requiredCall] at requiredDone
          cases requiredDone
          cases passCall : SourceCurrentAllocatedClassWorker.pass e p h m c n kept prepared
              (SourceCurrentConjunctionClassScan.advanceHeap checked preparedHeap) memo with
          | failed => simp only [SourceCurrentAllocatedLocalWorker.pass,passCall] at passDone; cases passDone
          | done final finalChecked finalMemo =>
            simp only [SourceCurrentAllocatedLocalWorker.pass,passCall] at passDone
            cases passDone
            by_cases selected : ∃ record ∈ kept, ∃ suffix, index :: suffix ∈ record.paths
            · obtain ⟨record,retained,suffix,member⟩ := selected
              have root := SourceCurrentSelectedRootOrigins.selected_root scanCall retained member input
              exact (SourceCurrentActualClassRowOrigins.prepared_pass requiredCall passCall effect.good
                (stored.grows effect.keeps) (fun value member => effect.keeps.available value (available value member))
                heap keptCoherent index childIndex
                (fun entries built => SourceCurrentRequiredPathFootprints.selected_records kept index childIndex keptUnselected built)
                keptUnselected input output root).2
            · have untouched : ∀ record ∈ kept, ∀ path ∈ record.paths,
                  ¬ [Int.ofNat index].IsPrefix (path.map Int.ofNat) := by
                intro record retained path member initial
                have natural := (SourceEqualityClassEdits.signed_prefix [index] path).mp initial
                obtain ⟨suffix,rfl⟩ := natural
                exact selected ⟨record,retained,suffix,member⟩
              have graph := (SourceEqualityRequiredExecution.requireAll_execution_iff _ _ _ _ _).mpr ⟨r,h,requiredCall⟩
              cases built : SourceEqualityNeeded.build
                  (SourceEqualitySelectedRequired.paths (kept.map SourceEqualityClassOrder.Record.paths)) with
              | node entries =>
                simp only [built] at graph
                have bound : index < prepared.length := graph.length ▸ (List.getElem?_eq_some_iff.mp input).choose
                let narrowed : Node := prepared[index]
                have narrowedInput : prepared[index]? = some narrowed := List.getElem?_eq_some_iff.mpr ⟨bound,rfl⟩
                have absent := SourceCurrentRequiredPathFootprints.selected_records_absent kept index untouched built
                have keptGet := SourceCurrentPositionalRowOrigins.required_children graph index (by simpa only [Nat.zero_add] using absent)
                have same : narrowed = source := Option.some.inj (narrowedInput.symm.trans (keptGet.trans input))
                have last := untouched_pass passCall keptCoherent index childIndex keptUnselected untouched narrowedInput output
                rcases last with empty | unchanged
                · cases empty
                  intro row impossible
                  cases impossible
                · cases unchanged.trans same
                  exact Link.refl _ _

end MicroCFTA.SourceCurrentActualLocalRowOrigins
