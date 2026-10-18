import MicroCFTA.SourceCurrentTargetMergeHistory
import MicroCFTA.SourceCurrentLowerOperationInvariants

/-!
# Historical Merge writers through actual class edits

Each literal successful edit retains the initial historical writer table.
The proof uses physical effects at the actual earlier child returns.
It does not assume semantic reads or construct general completion.
-/
namespace MicroCFTA.SourceCurrentLowerMergeHistory
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentNativeOperationHeap (Good)
open SourceCurrentMemoMergeEffects (Stored)
open SourceCurrentLowerOperationInvariants (Effect SharedGood)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Shared" => SourceCurrentAllocatedSharedTargetState.State
local notation "FieldAvailable" => SourceCurrentConjunctionEquality.FieldAvailable
local notation "Raw" => SourceCurrentMergePositiveRowOrigins.Raw SourceCurrentAllocatedMerge.literalClear
  (SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula))
variable {width : Nat}

private theorem shared_bind_done {A B : Type}
    (first : SourceCurrentAllocatedSharedEditWorker.Outcome width A)
    (next : A → Shared width → SourceCurrentAllocatedSharedEditWorker.Outcome width B)
    {output : B} {after : Shared width} (actual : first.bind next = .done output after) :
    ∃ value middle, first = .done value middle ∧ next value middle = .done output after := by
  cases first with
  | done value middle => exact ⟨value,middle,rfl,actual⟩
  | failed => cases actual

private theorem class_bind_done
    (first : SourceCurrentAllocatedClassWorker.Outcome width)
    (next : List Node → Checked width → Memo → SourceCurrentAllocatedClassWorker.Outcome width)
    {output : List Node} {after : Checked width} {saved : Memo} (actual : first.bind next = .done output after saved) :
    ∃ value middle current, first = .done value middle current ∧ next value middle current = .done output after saved := by
  cases first with
  | done value middle current => exact ⟨value,middle,current,rfl,actual⟩
  | failed => cases actual

private theorem shared_advance {before : Shared width} (good : SharedGood before) {checked : Checked width}
    (effect : Effect before.checked checked) : SharedGood (SourceCurrentAllocatedSharedTargetState.advance before checked) :=
  ⟨effect.good,good.stored.grows effect.keeps,
    fun path value present => effect.keeps.available value (good.slots path value present)⟩

private theorem same_operations {before : Checked width} (good : Good before)
    (heap : State Symbol Guard) (keeps : SourceEqualityRequiredCache.Keeps before.native.machine.heap heap)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady heap)
    (costs : InternedFreshOrdinaryCostHeap.Heap heap)
    (fields : SourceCurrentConjunctionEquality.Fields before.operations heap) :
    Effect before (advancePhysical before ⟨heap,before.operations⟩) :=
  let effects := (⟨keeps,⟨semantic,costs,good.operations,fields⟩,SourceEqualityConstraintMemoAllocation.grows_refl _⟩ :
    SourceCurrentConjunctionRowsAllocation.Effects (physical before) ⟨heap,before.operations⟩)
  ⟨good.advance _ effects,keeps,effects.grows⟩

private theorem edge_constructor [DecidableEq (EdgeKey Symbol Guard)] {before : Checked width}
    (good : Good before) (symbol : Symbol) (guard : Guard) (values : List Node)
    (field : FieldAvailable before.operations guard) (available : Values before.native.machine.heap values) :
    Effect before (advancePhysical before ⟨(run (makeEdge symbol guard values) before.native.machine.heap).2,before.operations⟩) := by
  have checked := SourceEqualityRequiredCache.edge symbol guard values _ good.heap available
  have semantic := SourceEqualityRequiredSemanticCache.edge symbol guard values _ good.semantic available
  have fields := SourceEqualityAnnotationHeap.run (FieldAvailable before.operations) _
    (SourceEqualityAnnotationHeap.makeEdge _ symbol guard values field) _ good.fields
  exact same_operations good _ checked.1 semantic good.costs fields

private theorem shared_head [DecidableEq (EdgeKey Symbol Guard)] {h value before result after}
    (actual : SourceCurrentAllocatedSharedEditWorker.head h value before = .done result after)
    (good : SharedGood (width := width) before) (available : Available before.checked.native.machine.heap value) :
    Effect before.checked after.checked ∧ SharedGood after ∧ Available after.checked.native.machine.heap result ∧ after.memo = before.memo := by
  cases returned : SourceEqualityRequiredWorker.head h value before.checked.native.machine.heap with
  | pending | unresolved | exhausted => simp only [SourceCurrentAllocatedSharedEditWorker.head,returned] at actual; cases actual
  | done output heap =>
    simp only [SourceCurrentAllocatedSharedEditWorker.head,returned] at actual
    cases actual
    have graph := SourceEqualityRequiredWorkerSound.head_graph h value _ _ heap returned
    obtain ⟨keeps,semantic,costs,fields,known⟩ := SourceCurrentRequiredHeapEffects.head
      (FieldAvailable before.checked.operations) graph good.checked.semantic good.checked.costs good.checked.fields available
    have effect := same_operations good.checked heap keeps semantic costs fields
    exact ⟨effect,shared_advance good effect,known,rfl⟩

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private def ChildContract (record : SourceEqualityClassOrder.Record)
    (originals : List Node) (e p h m s n : Nat) : Prop :=
  ∀ (edits : SourceEqualityEdits.Edits EqualityNormalize.Path) (value : Node) (before : Shared width) (output : Node) (after : Shared width),
    SourceCurrentAllocatedSharedEditWorker.edit record originals e p h m s n edits value before = .done output after →
    SharedGood before → Values before.checked.native.machine.heap originals → Available before.checked.native.machine.heap value →
    Raw before.memo → Raw after.memo

private theorem edit_children {record originals e p h m s n}
    (child : ChildContract (width := width) record originals e p h m s n) {entries index values before results after}
    (actual : SourceCurrentAllocatedSharedEditWorker.children
      (SourceCurrentAllocatedSharedEditWorker.edit record originals e p h m s n) entries index values before = .done results after)
    (good : SharedGood (width := width) before) (originalsAvailable : Values before.checked.native.machine.heap originals)
    (available : Values before.checked.native.machine.heap values) (raw : Raw before.memo) :
    Raw after.memo := by
  induction values generalizing index before results after with
  | nil => cases actual; exact raw
  | cons value values ih =>
    cases found : SourceEqualityNeededMap.lookup (index : Int) entries with
    | none =>
      simp only [SourceCurrentAllocatedSharedEditWorker.children,found] at actual
      obtain ⟨tail,final,rest,returned⟩ := shared_bind_done _ _ actual
      cases returned
      exact ih rest good originalsAvailable (fun value member => available value (List.mem_cons_of_mem _ member)) raw
    | some edits =>
      simp only [SourceCurrentAllocatedSharedEditWorker.children,found] at actual
      obtain ⟨result,middle,first,later⟩ := shared_bind_done _ _ actual
      obtain ⟨tail,final,rest,returned⟩ := shared_bind_done _ _ later
      cases returned
      obtain ⟨effect,current,known⟩ := SourceCurrentLowerOperationInvariants.edit first good originalsAvailable (available _ List.mem_cons_self)
      exact ih rest current (fun value member => effect.keeps.available value (originalsAvailable value member))
        (fun value member => effect.keeps.available value (available value (List.mem_cons_of_mem _ member)))
        (child edits value before result middle first good originalsAvailable (available _ List.mem_cons_self) raw)

private theorem edit_rows {record originals e p h m s n}
    (child : ChildContract (width := width) record originals e p h m s n) {entries rows before results after}
    (actual : SourceCurrentAllocatedSharedEditWorker.rows
      (SourceCurrentAllocatedSharedEditWorker.edit record originals e p h m s n) entries rows before = .done results after)
    (good : SharedGood (width := width) before) (originalsAvailable : Values before.checked.native.machine.heap originals)
    (resident : Edges before.checked.native.machine.heap rows) (raw : Raw before.memo) :
    Raw after.memo := by
  induction rows generalizing before results after with
  | nil => cases actual; exact raw
  | cons edge rows ih =>
    obtain ⟨values,middle,children,later⟩ := shared_bind_done _ _ actual
    have available := good.checked.heap.semantic.1.normal.facts.cached.edges _ _ (resident _ List.mem_cons_self)
    have childrenActual : SourceCurrentAllocatedSharedEditWorker.editList
        (SourceCurrentAllocatedSharedEditWorker.edit record originals e p h m s n)
        (.editBelow entries) edge.children before = .done values middle := children
    obtain ⟨firstEffect,current,known⟩ := SourceCurrentLowerOperationInvariants.edit_list childrenActual good originalsAvailable available
    have firstRaw := edit_children child children good originalsAvailable available raw
    obtain ⟨rebuilt,afterEdge,built,later⟩ := shared_bind_done _ _ later
    have field := (good.checked.fields _ _ (resident _ List.mem_cons_self)).grows firstEffect.operations
    have checked := edge_constructor current.checked edge.entry.key.symbol edge.entry.key.constraint values field known
    simp only [SourceCurrentAllocatedSharedEditWorker.work] at built
    cases built
    obtain ⟨tail,final,rest,returned⟩ := shared_bind_done _ _ later
    cases returned
    have edgeGood := shared_advance current checked
    have prefixEffect := firstEffect.trans checked
    exact ih rest edgeGood
      (fun value member => prefixEffect.keeps.available value (originalsAvailable value member))
      (fun edge member => edge_grows _ _ prefixEffect.keeps.growth edge (resident edge (List.mem_cons_of_mem _ member))) firstRaw

/-- A literal edit retains actual historical Merge writers at every returned memo key. -/
theorem edit {record originals e p h m s n edits value before result after}
    (actual : SourceCurrentAllocatedSharedEditWorker.edit record originals e p h m s n edits value before = .done result after)
    (good : SharedGood (width := width) before) (originalsAvailable : Values before.checked.native.machine.heap originals)
    (available : Available before.checked.native.machine.heap value) (raw : Raw before.memo) :
    Raw after.memo := by
  induction e generalizing edits value before result after with
  | zero => cases actual
  | succ e ih =>
    cases edits with
    | editAt path =>
      unfold SourceCurrentAllocatedSharedEditWorker.edit SourceCurrentAllocatedSharedEditWorker.leaf at actual
      cases observed : SourceCurrentAllocatedSharedTargetWorker.leaf p h m s n record originals path value before with
      | failed => simp only [observed,SourceCurrentAllocatedSharedEditWorker.lift] at actual; cases actual
      | done output middle =>
        simp only [observed,SourceCurrentAllocatedSharedEditWorker.lift] at actual
        cases actual
        exact SourceCurrentTargetMergeHistory.leaf observed good originalsAvailable raw
    | editBelow entries =>
      cases value with
      | empty => cases actual; exact raw
      | reference => cases actual
      | node entry rows depth free =>
        obtain ⟨rebuilt,middle,first,last⟩ := shared_bind_done _ _ actual
        have resident := resident_edges _ good.checked.heap.semantic.1.normal.facts.linked _ available.resident
        have retained := edit_rows (fun _ _ _ _ _ => ih) first good originalsAvailable resident raw
        simp only [SourceCurrentAllocatedSharedEditWorker.work] at last
        cases last
        exact retained
      | mu | union =>
        obtain ⟨exposed,middle,first,last⟩ := shared_bind_done _ _ actual
        obtain ⟨effect,current,known,sameMemo⟩ := shared_head first good available
        exact ih last current (fun value member => effect.keeps.available value (originalsAvailable value member)) known (sameMemo.symm ▸ raw)

/-- A completed edit list retains the historical writer table. -/
theorem edit_list {record originals e p h m s n edits values before results after}
    (actual : SourceCurrentAllocatedSharedEditWorker.editList
      (SourceCurrentAllocatedSharedEditWorker.edit record originals e p h m s n) edits values before = .done results after)
    (good : SharedGood (width := width) before) (originalsAvailable : Values before.checked.native.machine.heap originals)
    (available : Values before.checked.native.machine.heap values) (raw : Raw before.memo) :
    Raw after.memo := by
  cases edits with
  | editAt => cases actual; exact raw
  | editBelow entries => exact edit_children (fun _ _ _ _ _ => edit) actual good originalsAvailable available raw

/-- A completed class starts from empty target slots and retains Merge writers. -/
theorem run_class {e p h m s n record values before memo results after saved}
    (actual : SourceCurrentAllocatedClassWorker.runClass e p h m s n record values before memo = .done results after saved)
    (good : Good (width := width) before) (stored : Stored before.native.machine.heap memo)
    (available : Values before.native.machine.heap values) (raw : Raw memo) :
    Raw saved := by
  cases returned : SourceCurrentAllocatedSharedEditWorker.editList
      (SourceCurrentAllocatedSharedEditWorker.edit record values e p h m s n)
      (SourceCurrentAllocatedClassEditPlan.compiled record) values (SourceCurrentAllocatedSharedTargetState.initial before memo) with
  | failed => simp only [SourceCurrentAllocatedClassWorker.runClass,returned] at actual; cases actual
  | done output shared =>
    simp only [SourceCurrentAllocatedClassWorker.runClass,returned] at actual
    cases actual
    exact edit_list returned (SharedGood.initial good stored) available available raw

/-- The actual class right fold retains writers through its tail and head calls. -/
theorem class_fold {e p h m s n records values before memo results after saved}
    (actual : SourceCurrentAllocatedClassWorker.fold e p h m s n records values before memo = .done results after saved)
    (good : Good (width := width) before) (stored : Stored before.native.machine.heap memo)
    (available : Values before.native.machine.heap values) (raw : Raw memo) :
    Raw saved := by
  induction records generalizing values before memo results after saved with
  | nil => cases actual; exact raw
  | cons record records ih =>
    obtain ⟨middle,checked,current,first,last⟩ := class_bind_done _ _ actual
    obtain ⟨effect,retained,known⟩ := SourceCurrentLowerOperationInvariants.class_fold first good stored available
    exact run_class last effect.good retained known (ih first good stored available raw)

/-- Final value propagation retains the Merge table. -/
theorem class_pass {e p h m s n records values before memo results after saved}
    (actual : SourceCurrentAllocatedClassWorker.pass e p h m s n records values before memo = .done results after saved)
    (good : Good (width := width) before) (stored : Stored before.native.machine.heap memo)
    (available : Values before.native.machine.heap values) (raw : Raw memo) :
    Raw saved := by
  obtain ⟨middle,checked,current,first,last⟩ := class_bind_done _ _ actual
  cases last
  exact class_fold first good stored available raw

end MicroCFTA.SourceCurrentLowerMergeHistory
