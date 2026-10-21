import MicroCFTA.SourceCurrentOuterMergeHistory
import MicroCFTA.SourceCurrentMergePositivePosition

/-!
# Positive-position Merge support at actual outer prefixes

The proof follows successful lower calls and actual unfinished outer phases.
It does not cover an internal failed Parent or failed Merge return.
The current table law does not supply the law at a historical writer entry.
-/
namespace MicroCFTA.SourceCurrentOuterMergePositionSupport
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeEffects (physical)
open InternedNestedProvenance (Values)
open SourceCurrentNativeOperationHeap (Good)
open SourceCurrentLowerOperationInvariants (SharedGood)
open SourceCurrentMemoMergeEffects (Stored)
open SourceCurrentMergePositivePosition (Support)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "literalClear" => SourceCurrentAllocatedMerge.literalClear
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
variable [symbolEq : DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

private theorem operand {p h m s path values before memo result after saved}
    (actual : SourceCurrentAllocatedTargetWorker.operand p h m s path values before memo = .done result after saved)
    (good : Good (width := width) before) (stored : Stored before.native.machine.heap memo)
    (available : Values before.native.machine.heap values) (support : Support memo) :
    Support saved := by
  have same : symbolEq = @instDecidableEqProd SourceGuards.Name FullSyntax.Formula
      instDecidableEqString FormulaExecutable.formulaDecidableEq := Subsingleton.elim _ _
  cases same
  letI : DecidableEq Symbol := @instDecidableEqProd SourceGuards.Name FullSyntax.Formula
    instDecidableEqString FormulaExecutable.formulaDecidableEq
  obtain ⟨projected,middle,current,projectionDone,mergeDone⟩ :=
    (SourceCurrentAllocatedTargetWorkerSound.bind_done _ _ result after saved).mp actual
  obtain ⟨heap,graph,shape,sameMemo⟩ := SourceCurrentAllocatedTargetWorkerSound.projection_sound
    p h path values before memo projected middle current projectionDone
  subst current
  have facts := SourceEqualityProjectionCosts.forest_effects graph good.semantic good.costs available
  have middleHeap : middle.native.machine.heap = heap := by rw [shape]; rfl
  have currentSemantic : SourceEqualityRequiredSemanticCache.SemanticReady middle.native.machine.heap := by
    simpa only [middleHeap] using facts.2.1
  have currentCosts : InternedFreshOrdinaryCostHeap.Heap middle.native.machine.heap := by
    simpa only [middleHeap] using facts.2.2.1
  have currentStored : Stored middle.native.machine.heap memo := by
    simpa only [middleHeap] using stored.grows facts.1
  have currentAvailable : Available middle.native.machine.heap projected := by
    simpa only [middleHeap] using facts.2.2.2
  cases called : SourceCurrentAllocatedMergeWorker.call literalClear m s projected (physical middle) memo with
  | failed =>
      simp only [SourceCurrentAllocatedTargetWorker.merge,called] at mergeDone
      cases mergeDone
  | done output final current =>
      simp only [SourceCurrentAllocatedTargetWorker.merge,called] at mergeDone
      cases mergeDone
      exact (SourceCurrentMergePositivePosition.allocated literalClear called currentSemantic currentCosts
        currentStored support currentAvailable).2.2.1

private theorem target_leaf_memo {n left right memo result saved} {before after : Checked width}
    (actual : SourceCurrentAllocatedTargetWorker.leaf n left right before memo = .done result after saved) :
    saved = memo := by
  cases observed : SourceEqualityNativeDemand.execute n
      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) before with
  | done value checked =>
    simp only [SourceCurrentAllocatedTargetWorker.leaf,observed] at actual
    cases actual
    rfl
  | yielded | failed | constraintError | blocked =>
    simp only [SourceCurrentAllocatedTargetWorker.leaf,observed] at actual
    cases actual

private theorem fold {p h m s n values seed paths before memo result after saved}
    (actual : SourceCurrentAllocatedTargetWorker.fold p h m s n values seed paths before memo = .done result after saved)
    (good : Good (width := width) before) (stored : Stored before.native.machine.heap memo)
    (available : Values before.native.machine.heap values) (support : Support memo) :
    Support saved := by
  induction paths generalizing before memo result after saved with
  | nil => exact operand actual good stored available support
  | cons path paths ih =>
    obtain ⟨head,middle,current,first,later⟩ :=
      (SourceCurrentAllocatedTargetWorkerSound.bind_done _ _ result after saved).mp actual
    have headSupport := operand first good stored available support
    obtain ⟨headEffect,headStored,_headAvailable⟩ :=
      SourceCurrentLowerOperationInvariants.operand first good stored available
    obtain ⟨tail,final,completed,rest,last⟩ :=
      (SourceCurrentAllocatedTargetWorkerSound.bind_done _ _ result after saved).mp later
    have tailSupport := ih rest headEffect.good headStored
      (fun value member => headEffect.keeps.available value (available value member)) headSupport
    exact (target_leaf_memo last) ▸ tailSupport

private theorem target {p h m s n values paths before memo result after saved}
    (actual : SourceCurrentAllocatedTargetWorker.target p h m s n values paths before memo = .done result after saved)
    (good : Good (width := width) before) (stored : Stored before.native.machine.heap memo)
    (available : Values before.native.machine.heap values) (support : Support memo) :
    Support saved := by
  cases paths with
  | nil => cases actual; exact support
  | cons seed paths => exact fold actual good stored available support

private theorem force {p h m s n record originals path before result after}
    (actual : SourceCurrentAllocatedSharedTargetWorker.force p h m s n record originals path before = .done result after)
    (good : SharedGood (width := width) before)
    (available : Values before.checked.native.machine.heap originals)
    (support : Support before.memo) : Support after.memo := by
  cases found : before.targets path with
  | some value =>
    simp only [SourceCurrentAllocatedSharedTargetWorker.force,found] at actual
    cases actual
    exact support
  | none =>
    cases returned : SourceCurrentAllocatedTargetWorker.target p h m s n originals
        (SourceEqualityClassTarget.operandPaths record.paths path) before.checked before.memo with
    | failed =>
      simp only [SourceCurrentAllocatedSharedTargetWorker.force,found,returned] at actual
      cases actual
    | done value checked saved =>
      simp only [SourceCurrentAllocatedSharedTargetWorker.force,found,returned] at actual
      cases actual
      exact target returned good.checked good.stored available support

private theorem leaf {p h m s n record originals path input before result after}
    (actual : SourceCurrentAllocatedSharedTargetWorker.leaf p h m s n record originals path input before = .done result after)
    (good : SharedGood (width := width) before)
    (available : Values before.checked.native.machine.heap originals)
    (support : Support before.memo) : Support after.memo := by
  cases first : SourceCurrentAllocatedSharedTargetWorker.force p h m s n record originals path before with
  | failed =>
    simp only [SourceCurrentAllocatedSharedTargetWorker.leaf,first,
      SourceCurrentAllocatedSharedTargetWorker.Outcome.bind] at actual
    cases actual
  | done value middle =>
    simp only [SourceCurrentAllocatedSharedTargetWorker.leaf,first,
      SourceCurrentAllocatedSharedTargetWorker.Outcome.bind] at actual
    have retained := force first good available support
    have same := (SourceCurrentAllocatedSharedTargetWorker.step_state n value input middle).2.2
    rw [actual] at same
    exact same ▸ retained

end MicroCFTA.SourceCurrentOuterMergePositionSupport

namespace MicroCFTA.SourceCurrentOuterMergePositionSupport
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
open SourceCurrentMergePositivePosition (Support)
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
    Support before.memo → Support after.memo

private theorem edit_children {record originals e p h m s n}
    (child : ChildContract (width := width) record originals e p h m s n) {entries index values before results after}
    (actual : SourceCurrentAllocatedSharedEditWorker.children
      (SourceCurrentAllocatedSharedEditWorker.edit record originals e p h m s n) entries index values before = .done results after)
    (good : SharedGood (width := width) before) (originalsAvailable : Values before.checked.native.machine.heap originals)
    (available : Values before.checked.native.machine.heap values) (support : Support before.memo) :
    Support after.memo := by
  induction values generalizing index before results after with
  | nil => cases actual; exact support
  | cons value values ih =>
    cases found : SourceEqualityNeededMap.lookup (index : Int) entries with
    | none =>
      simp only [SourceCurrentAllocatedSharedEditWorker.children,found] at actual
      obtain ⟨tail,final,rest,returned⟩ := shared_bind_done _ _ actual
      cases returned
      exact ih rest good originalsAvailable (fun value member => available value (List.mem_cons_of_mem _ member)) support
    | some edits =>
      simp only [SourceCurrentAllocatedSharedEditWorker.children,found] at actual
      obtain ⟨result,middle,first,later⟩ := shared_bind_done _ _ actual
      obtain ⟨tail,final,rest,returned⟩ := shared_bind_done _ _ later
      cases returned
      obtain ⟨effect,current,known⟩ := SourceCurrentLowerOperationInvariants.edit first good originalsAvailable (available _ List.mem_cons_self)
      exact ih rest current (fun value member => effect.keeps.available value (originalsAvailable value member))
        (fun value member => effect.keeps.available value (available value (List.mem_cons_of_mem _ member)))
        (child edits value before result middle first good originalsAvailable (available _ List.mem_cons_self) support)

private theorem edit_rows {record originals e p h m s n}
    (child : ChildContract (width := width) record originals e p h m s n) {entries rows before results after}
    (actual : SourceCurrentAllocatedSharedEditWorker.rows
      (SourceCurrentAllocatedSharedEditWorker.edit record originals e p h m s n) entries rows before = .done results after)
    (good : SharedGood (width := width) before) (originalsAvailable : Values before.checked.native.machine.heap originals)
    (resident : Edges before.checked.native.machine.heap rows) (support : Support before.memo) :
    Support after.memo := by
  induction rows generalizing before results after with
  | nil => cases actual; exact support
  | cons edge rows ih =>
    obtain ⟨values,middle,children,later⟩ := shared_bind_done _ _ actual
    have available := good.checked.heap.semantic.1.normal.facts.cached.edges _ _ (resident _ List.mem_cons_self)
    have childrenActual : SourceCurrentAllocatedSharedEditWorker.editList
        (SourceCurrentAllocatedSharedEditWorker.edit record originals e p h m s n)
        (.editBelow entries) edge.children before = .done values middle := children
    obtain ⟨firstEffect,current,known⟩ := SourceCurrentLowerOperationInvariants.edit_list childrenActual good originalsAvailable available
    have firstSupport := edit_children child children good originalsAvailable available support
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
      (fun edge member => edge_grows _ _ prefixEffect.keeps.growth edge (resident edge (List.mem_cons_of_mem _ member))) firstSupport

private theorem edit {record originals e p h m s n edits value before result after}
    (actual : SourceCurrentAllocatedSharedEditWorker.edit record originals e p h m s n edits value before = .done result after)
    (good : SharedGood (width := width) before) (originalsAvailable : Values before.checked.native.machine.heap originals)
    (available : Available before.checked.native.machine.heap value) (support : Support before.memo) :
    Support after.memo := by
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
        exact SourceCurrentOuterMergePositionSupport.leaf observed good originalsAvailable support
    | editBelow entries =>
      cases value with
      | empty => cases actual; exact support
      | reference => cases actual
      | node entry rows depth free =>
        obtain ⟨rebuilt,middle,first,last⟩ := shared_bind_done _ _ actual
        have resident := resident_edges _ good.checked.heap.semantic.1.normal.facts.linked _ available.resident
        have retained := edit_rows (fun _ _ _ _ _ => ih) first good originalsAvailable resident support
        simp only [SourceCurrentAllocatedSharedEditWorker.work] at last
        cases last
        exact retained
      | mu | union =>
        obtain ⟨exposed,middle,first,last⟩ := shared_bind_done _ _ actual
        obtain ⟨effect,current,known,sameMemo⟩ := shared_head first good available
        exact ih last current (fun value member => effect.keeps.available value (originalsAvailable value member)) known (sameMemo.symm ▸ support)

private theorem edit_list {record originals e p h m s n edits values before results after}
    (actual : SourceCurrentAllocatedSharedEditWorker.editList
      (SourceCurrentAllocatedSharedEditWorker.edit record originals e p h m s n) edits values before = .done results after)
    (good : SharedGood (width := width) before) (originalsAvailable : Values before.checked.native.machine.heap originals)
    (available : Values before.checked.native.machine.heap values) (support : Support before.memo) :
    Support after.memo := by
  cases edits with
  | editAt => cases actual; exact support
  | editBelow entries => exact edit_children (fun _ _ _ _ _ => edit) actual good originalsAvailable available support

private theorem run_class {e p h m s n record values before memo results after saved}
    (actual : SourceCurrentAllocatedClassWorker.runClass e p h m s n record values before memo = .done results after saved)
    (good : Good (width := width) before) (stored : Stored before.native.machine.heap memo)
    (available : Values before.native.machine.heap values) (support : Support memo) :
    Support saved := by
  cases returned : SourceCurrentAllocatedSharedEditWorker.editList
      (SourceCurrentAllocatedSharedEditWorker.edit record values e p h m s n)
      (SourceCurrentAllocatedClassEditPlan.compiled record) values (SourceCurrentAllocatedSharedTargetState.initial before memo) with
  | failed => simp only [SourceCurrentAllocatedClassWorker.runClass,returned] at actual; cases actual
  | done output shared =>
    simp only [SourceCurrentAllocatedClassWorker.runClass,returned] at actual
    cases actual
    exact edit_list returned (SharedGood.initial good stored) available available support

private theorem class_fold {e p h m s n records values before memo results after saved}
    (actual : SourceCurrentAllocatedClassWorker.fold e p h m s n records values before memo = .done results after saved)
    (good : Good (width := width) before) (stored : Stored before.native.machine.heap memo)
    (available : Values before.native.machine.heap values) (support : Support memo) :
    Support saved := by
  induction records generalizing values before memo results after saved with
  | nil => cases actual; exact support
  | cons record records ih =>
    obtain ⟨middle,checked,current,first,last⟩ := class_bind_done _ _ actual
    obtain ⟨effect,retained,known⟩ := SourceCurrentLowerOperationInvariants.class_fold first good stored available
    exact run_class last effect.good retained known (ih first good stored available support)

private theorem class_pass {e p h m s n records values before memo results after saved}
    (actual : SourceCurrentAllocatedClassWorker.pass e p h m s n records values before memo = .done results after saved)
    (good : Good (width := width) before) (stored : Stored before.native.machine.heap memo)
    (available : Values before.native.machine.heap values) (support : Support memo) :
    Support saved := by
  obtain ⟨middle,checked,current,first,last⟩ := class_bind_done _ _ actual
  cases last
  exact class_fold first good stored available support

end MicroCFTA.SourceCurrentOuterMergePositionSupport

namespace MicroCFTA.SourceCurrentOuterMergePositionSupport
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentNativeOperationHeap (Good)
open SourceCurrentLowerOperationInvariants (Effect)
open SourceCurrentMemoMergeEffects (Stored)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "FieldAvailable" => SourceCurrentConjunctionEquality.FieldAvailable
open SourceCurrentMergePositivePosition (Support)
variable {width : Nat}

private theorem physical_only {before : Checked width} (good : Good before)
    (heap : State Symbol Guard) (keeps : SourceEqualityRequiredCache.Keeps before.native.machine.heap heap)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady heap)
    (costs : InternedFreshOrdinaryCostHeap.Heap heap)
    (fields : SourceCurrentConjunctionEquality.Fields before.operations heap) :
    Effect before (advancePhysical before ⟨heap,before.operations⟩) :=
  let effects := (⟨keeps,⟨semantic,costs,good.operations,fields⟩,SourceEqualityConstraintMemoAllocation.grows_refl _⟩ :
    SourceCurrentConjunctionRowsAllocation.Effects (physical before) ⟨heap,before.operations⟩)
  ⟨good.advance _ effects,keeps,effects.grows⟩

private theorem local_bind_done {A B : Type}
    (first : SourceCurrentAllocatedLocalWorker.Outcome A width)
    (next : A → Checked width → Fourth → Memo → SourceCurrentAllocatedLocalWorker.Outcome B width)
    {output : B} {after : Checked width} {fourth : Fourth} {saved : Memo}
    (actual : first.bind next = .done output after fourth saved) :
    ∃ value middle current memo, first = .done value middle current memo ∧ next value middle current memo = .done output after fourth saved := by
  cases first with
  | done value middle current memo => exact ⟨value,middle,current,memo,rfl,actual⟩
  | failed => cases actual

private theorem local_scan [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
    {g s p h n budget records values before fourth memo result after saved current}
    (actual : SourceCurrentAllocatedLocalWorker.scan g s p h n budget records values before fourth memo = .done result after saved current)
    (good : Good (width := width) before) (available : Values before.native.machine.heap values) :
    Effect before after ∧ current = memo := by
  cases observed : SourceCurrentAllocatedRecordScanWorker.scan g s p h n budget values records before fourth with
  | failed => simp only [SourceCurrentAllocatedLocalWorker.scan,observed] at actual; cases actual
  | done output checked completed =>
    simp only [SourceCurrentAllocatedLocalWorker.scan,observed] at actual
    cases actual
    have paths := (SourceCurrentAllocatedRecordScanWorker.scan_mapPaths g s p h n budget values records before fourth).symm
    rw [observed] at paths
    exact ⟨SourceCurrentParentOperationInvariants.scan paths good available,rfl⟩

private theorem local_required [DecidableEq (EdgeKey Symbol Guard)]
    {r h paths values before fourth memo results after saved current}
    (actual : SourceCurrentAllocatedLocalWorker.required r h paths values before fourth memo = .done results after saved current)
    (good : Good (width := width) before) (available : Values before.native.machine.heap values) :
    Effect before after ∧ Values after.native.machine.heap results ∧ saved = fourth ∧ current = memo := by
  cases observed : SourceEqualityRequiredExecution.requireAll r h paths values before.native.machine.heap with
  | pending | unresolved | exhausted => simp only [SourceCurrentAllocatedLocalWorker.required,observed] at actual; cases actual
  | done output heap =>
    simp only [SourceCurrentAllocatedLocalWorker.required,observed] at actual
    cases actual
    obtain ⟨keeps,semantic,costs,fields,known⟩ := SourceCurrentRequiredHeapEffects.requireAll
      (FieldAvailable before.operations) r h paths values _ _ heap observed good.semantic good.costs good.fields available
    exact ⟨physical_only good heap keeps semantic costs fields,known,rfl,rfl⟩

private theorem local_pass [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {e p h m s n records values before fourth memo results after saved current}
    (actual : SourceCurrentAllocatedLocalWorker.pass e p h m s n records values before fourth memo = .done results after saved current)
    (good : Good (width := width) before) (stored : Stored before.native.machine.heap memo)
    (available : Values before.native.machine.heap values)
    (support : Support memo) : Support current := by
  cases observed : SourceCurrentAllocatedClassWorker.pass e p h m s n records values before memo with
  | failed => simp only [SourceCurrentAllocatedLocalWorker.pass,observed] at actual; cases actual
  | done output checked completed =>
    simp only [SourceCurrentAllocatedLocalWorker.pass,observed] at actual
    cases actual
    exact SourceCurrentOuterMergePositionSupport.class_pass observed good stored available support

private theorem classes [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
    {g s r e p h m c n budget records values before fourth memo results after saved current}
    (actual : SourceCurrentAllocatedLocalWorker.classes g s r e p h m c n budget records values before fourth memo = .done results after saved current)
    (good : Good (width := width) before) (stored : Stored before.native.machine.heap memo)
    (available : Values before.native.machine.heap values)
    (support : Support memo) : Support current := by
  obtain ⟨result,middle,completed,current,first,later⟩ := local_bind_done _ _ actual
  obtain ⟨effect,rfl⟩ := local_scan first good available
  cases stopped : result.1 with
  | some paths => simp only [stopped] at later; cases later; exact support
  | none =>
    simp only [stopped] at later
    obtain ⟨required,checked,following,warm,requiredDone,passDone⟩ := local_bind_done _ _ later
    obtain ⟨firstEffect,known,_,rfl⟩ := local_required requiredDone effect.good
      (fun value member => effect.keeps.available value (available value member))
    exact local_pass passDone firstEffect.good (stored.grows (effect.keeps.trans firstEffect.keeps)) known support

private theorem precheck_good (loaded : Allocated) (inherited : EqValue) (before : Checked width)
    (good : Good before) (stored : EqReady before.operations.constraints loaded.stored)
    (ready : EqReady before.operations.constraints inherited) :
    Good (SourceCurrentAllocatedPrecheck.state before loaded inherited) := by
  obtain ⟨own,done,valid,ownReady,_,growth⟩ := SourceEqualityAccessorAllocation.equalities_correct
    loaded.stored loaded.guard before.operations good.operations stored
  have checked := SourceEqualityPrecheckAllocation.precheck_correct own inherited
    (SourceEqualityAccessorAllocation.equalities loaded.stored loaded.guard before.operations).2 valid ownReady
    (ready.grows growth.constraint_growth)
  have same : SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard inherited before.operations =
      SourceEqualityPrecheckAllocation.precheck own inherited
        (SourceEqualityAccessorAllocation.equalities loaded.stored loaded.guard before.operations).2 := by
    simp only [SourceEqualityPartialPrecheckAllocation.run,done]
  have total := SourceCurrentConjunctionEquality.grows_trans growth checked.2.2
  apply good.advance
  rw [same]
  exact ⟨SourceEqualityRequiredCache.pure_keeps _ good.heap,
    ⟨good.semantic,good.costs,checked.2.1,good.fields.grows total⟩,total⟩

private theorem reduce [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
    {g s r e p h m c n budget loaded inherited values before fourth memo results after saved current}
    (actual : SourceCurrentAllocatedLocalWorker.reduce g s r e p h m c n budget loaded inherited values before fourth memo = .done results after saved current)
    (good : Good (width := width) before) (stored : Stored before.native.machine.heap memo)
    (loadedReady : EqReady before.operations.constraints loaded.stored)
    (inheritedReady : EqReady before.operations.constraints inherited) (available : Values before.native.machine.heap values)
    (support : Support memo) : Support current := by
  have currentGood := precheck_good loaded inherited before good loadedReady inheritedReady
  cases observed : (SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard inherited before.operations).1 with
  | error message => simp only [SourceCurrentAllocatedLocalWorker.reduce,observed] at actual; cases actual
  | ok branch =>
    cases branch with
    | unchanged | emptyChildren =>
      simp only [SourceCurrentAllocatedLocalWorker.reduce,observed] at actual
      cases actual
      exact support
    | classes records =>
      simp only [SourceCurrentAllocatedLocalWorker.reduce,observed] at actual
      exact classes actual currentGood stored available support

private theorem parent_bind_done {A B : Type}
    (first : SourceCurrentAllocatedParentWorker.Outcome A width)
    (next : A → Checked width → Fourth → Memo → SourceCurrentAllocatedParentWorker.Outcome B width)
    {output : B} {after : Checked width} {fourth : Fourth} {saved : Memo}
    (actual : first.bind next = .done output after fourth saved) :
    ∃ value middle current memo, first = .done value middle current memo ∧ next value middle current memo = .done output after fourth saved := by
  cases first with
  | done value middle current memo => exact ⟨value,middle,current,memo,rfl,actual⟩
  | failed => cases actual

/-- A completed literal Parent call preserves its initial Merge support law. -/
theorem parent [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
    {g s r e p h m c n budget symbol original inherited children before fourth memo result after saved current}
    (actual : SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget symbol original inherited children before fourth memo =
      .done result after saved current)
    (good : Good (width := width) before) (stored : Stored before.native.machine.heap memo)
    (support : Support memo)
    (live : SourceEqualityMkEdgeAllocation.contradictory original = false →
      FieldAvailable before.operations original ∧ EqReady before.operations.constraints inherited ∧ Values before.native.machine.heap children) :
    Support current := by
  cases rejected : SourceEqualityMkEdgeAllocation.contradictory original with
  | true =>
    simp only [SourceCurrentAllocatedParentWorker.edge,rejected,ite_true] at actual
    cases actual
    exact support
  | false =>
    obtain ⟨field,inheritedReady,available⟩ := live rejected
    simp only [SourceCurrentAllocatedParentWorker.edge,rejected,Bool.false_eq_true,ite_false] at actual
    cases loaded : SourceEqualityConstraintFieldLookup.load original before.operations.constraints with
    | error => simp only [loaded] at actual; cases actual
    | ok value =>
      cases value with
      | none => simp only [loaded] at actual; cases actual
      | some loadedValue =>
        simp only [loaded] at actual
        obtain ⟨values,middle,completed,warm,first,last⟩ := parent_bind_done _ _ actual
        have properties := SourceEqualityConstraintFieldLookup.load_ready original before.operations.constraints
          good.operations.constraints field.1 loadedValue loaded
        have reduced : SourceCurrentAllocatedLocalWorker.reduce g s r e p h m c n budget
            loadedValue inherited children before fourth memo = .done values middle completed warm := by
          cases observed : SourceCurrentAllocatedLocalWorker.reduce g s r e p h m c n budget
              loadedValue inherited children before fourth memo with
          | failed => simp only [SourceCurrentAllocatedParentWorker.reduceChildren,observed] at first; cases first
          | done output checked next current =>
            simp only [SourceCurrentAllocatedParentWorker.reduceChildren,observed] at first
            cases first
            rfl
        have middleSupport := reduce reduced good stored properties.1 inheritedReady available support
        cases observed : SourceCurrentAllocatedMkEdge.build symbol loadedValue values middle with
        | mk returned checked =>
          cases returned with
          | error => simp only [SourceCurrentAllocatedParentWorker.build,observed] at last; cases last
          | ok value =>
            simp only [SourceCurrentAllocatedParentWorker.build,observed] at last
            cases last
            exact middleSupport

end MicroCFTA.SourceCurrentOuterMergePositionSupport

namespace MicroCFTA.SourceCurrentOuterMergePositionSupport
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialWorker
open SourceCurrentOuterPrefixInvariants (Good NodeReady EdgeReady Inputs)
open SourceCurrentOuterCopiedWarmHit (Phase)
open SourceCurrentOuterExecutionAncestry (Step Reached)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
open SourceCurrentMergePositivePosition (Support)
local notation "literalClear" => SourceCurrentAllocatedMerge.literalClear
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "caller" => SourceCurrentOuterActiveAncestry.caller
variable {width : Nat}

private theorem demand_valid (handle : Nat) (state : FlatMemoThunk.State Key Request Result)
    (keyOf : Request → Key → Prop) (property : FlatMemoThunk.Cell Request Result → Prop)
    (valid : FlatMemoThunk.Valid keyOf property state)
    (started : ∀ request, property ⟨request,.suspended⟩ → property ⟨request,.evaluating⟩) :
    FlatMemoThunk.Valid keyOf property (FlatMemoThunk.demand handle state).2 := by
  cases found : state.cells handle with
  | none => simpa only [FlatMemoThunk.demand,found] using valid
  | some cell =>
    cases cell with
    | mk request status =>
      cases status with
      | evaluating | returned value => simpa only [FlatMemoThunk.demand,found] using valid
      | suspended =>
        simp only [FlatMemoThunk.demand,found]
        exact FlatMemoThunk.setStatus_valid _ _ _ _ _ valid _ found (started request (valid.checked _ _ found))

private theorem begin_good (request : EdgeRequest) {before : Caller width}
    (good : Good before) (ready : EdgeReady before request) : Good (beginEdge request before).2.2 := by
  refine ⟨good.checked,good.stored,good.probes,good.nodes,?_⟩
  apply demand_valid
  · exact FlatMemoThunk.lookup_valid _ _ _ _ _ good.edges rfl
      ⟨ready,by intro value impossible; cases impossible⟩
  · intro owner supported
    exact ⟨supported.1,by intro value impossible; cases impossible⟩

private theorem bind_done (first : Outcome A width) (next : A → Caller width → Outcome B width)
    (actual : first.bind next = .done value after) :
    ∃ result middle, first = .done result middle ∧ next result middle = .done value after := by
  cases first with
  | done result middle => exact ⟨result,middle,rfl,actual⟩
  | failed => cases actual

variable [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Guard)]

variable [DecidableEq Symbol]

variable [DecidableEq Node]

private theorem edge_body_done {fuel g s r e p h m c n budget request before value after}
    (actual : edgeBody fuel g s r e p h m c n budget request before = .done value after)
    (good : Good (width := width) before) (ready : EdgeReady before request)
    (support : Support before.merge) : Support after.merge := by
  cases observed : SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget
      request.value.entry.key.symbol request.value.entry.key.constraint request.inherited request.value.children
      before.checked before.fourth before.merge with
  | failed => simp only [edgeBody,observed] at actual; cases actual
  | done result checked fourth memo =>
    simp only [edgeBody,observed] at actual
    cases actual
    exact SourceCurrentOuterMergePositionSupport.parent observed good.checked good.stored support
      (fun _ => ⟨good.checked.fields request.value.entry.key request.value ready.2,ready.1,
        good.checked.semantic.ready.semantic.1.normal.facts.cached.edges _ _ ready.2⟩)

private theorem edge_done {fuel g s r e p h m c n budget request before value after}
    (actual : edgeCall fuel g s r e p h m c n budget request before = .done value after)
    (good : Good (width := width) before) (ready : EdgeReady before request)
    (support : Support before.merge) : Support after.merge := by
  rcases started : beginEdge request before with ⟨handle,action,running⟩
  have initial := begin_good request good ready
  have same := (beginEdge_components request before).2.1
  rw [started] at initial same
  have initialSupport : Support running.merge := by rw [same]; exact support
  cases action with
  | busy | absent => simp only [edgeCall,started] at actual; cases actual
  | ready result =>
    simp only [edgeCall,started] at actual
    cases actual
    exact initialSupport
  | evaluate owner =>
    let published := FlatMemoThunk.lookupOrInsert request.key request before.edgeResults
    have observed := congrArg (fun result => (result.2.1,result.2.2.edgeResults)) started
    change FlatMemoThunk.demand published.1 published.2 = (.evaluate owner,running.edgeResults) at observed
    have found := (FlatMemoThunk.demand_evaluate _ _ _ owner observed).2
    have handles : published.1 = handle := congrArg Prod.fst started
    rw [handles] at found
    obtain ⟨result,middle,body,finished⟩ := bind_done _ _ (by simpa only [edgeCall,started] using actual)
    cases finished
    change Support middle.merge
    exact edge_body_done body initial (initial.edges.checked _ _ found).1 initialSupport

private def NodeAt (fuel : Nat) : Prop := ∀ {g s r e p h m c n budget request before value after},
  nodeCall fuel g s r e p h m c n budget request before = .done value after → Good (width := width) before → NodeReady before request →
    Support before.merge → Support after.merge
private def BodyAt (fuel : Nat) : Prop := ∀ {g s r e p h m c n budget request before value after},
  nodeBody fuel g s r e p h m c n budget request before = .done value after → Good (width := width) before → NodeReady before request →
    Support before.merge → Support after.merge
private def RowsAt (fuel : Nat) : Prop := ∀ {g s r e p h m c n budget inherited values before result after},
  rows fuel g s r e p h m c n budget inherited values before = .done result after → Good (width := width) before →
    EqReady before.checked.operations.constraints inherited → Edges before.checked.native.machine.heap values →
    Support before.merge → Support after.merge
private def DescendantsAt (fuel : Nat) : Prop := ∀ {g s r e p h m c n budget inherited value before result after},
  descendants fuel g s r e p h m c n budget inherited value before = .done result after → Good (width := width) before →
    EqReady before.checked.operations.constraints inherited → EdgeResident before.checked.native.machine.heap value →
    Support before.merge → Support after.merge
private def ChildrenAt (fuel : Nat) : Prop := ∀ {g s r e p h m c n budget inherited values before result after},
  children fuel g s r e p h m c n budget inherited values before = .done result after → Good (width := width) before →
    EqReady before.checked.operations.constraints inherited → Values before.checked.native.machine.heap values →
    Support before.merge → Support after.merge
private def WalkAt (fuel : Nat) : Prop := ∀ {g s r e p h m c n budget inherited index values before result after},
  walk fuel g s r e p h m c n budget inherited index values before = .done result after → Good (width := width) before →
    EqReady before.checked.operations.constraints inherited → Values before.checked.native.machine.heap values →
    Support before.merge → Support after.merge

private theorem all_done (fuel : Nat) :
    NodeAt (width := width) fuel ∧ BodyAt (width := width) fuel ∧ RowsAt (width := width) fuel ∧
      DescendantsAt (width := width) fuel ∧ ChildrenAt (width := width) fuel ∧ WalkAt (width := width) fuel := by
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    have walkAt : WalkAt (width := width) fuel := by
      intro g s r e p h m c n budget inherited index values before result after actual good ready available support
      cases values with
      | nil => simp only [walk] at actual; cases actual; exact support
      | cons value values =>
        cases fuel with
        | zero => simp only [walk] at actual; cases actual
        | succ fuel =>
          obtain ⟨head,middle,first,later⟩ := bind_done _ _ (by simpa only [walk] using actual)
          have start := SourceCurrentOuterPrefixInvariants.reached
            (g := g) (s := s) (r := r) (e := e) (p := p) (h := h) (m := m) (c := c) (n := n) (budget := budget)
            (first := .walk (fuel+1) inherited index (value :: values) before)
            (last := .node fuel ⟨(SourceCurrentAllocatedPartialGraph.descend before inherited index).1,value⟩
              (SourceCurrentAllocatedPartialGraph.descend before inherited index).2)
            (.snoc (.refl _) .walk_head) good ⟨ready,available⟩
          have headSupport := (ih fuel (Nat.lt_succ_self _)).1 first start.1 start.2 (by exact support)
          obtain ⟨tail,final,rest,last⟩ := bind_done _ _ later
          cases last
          have resumed := SourceCurrentOuterPrefixInvariants.reached
            (g := g) (s := s) (r := r) (e := e) (p := p) (h := h) (m := m) (c := c) (n := n) (budget := budget)
            (first := .walk (fuel+1) inherited index (value :: values) before)
            (last := .walk fuel inherited (index+1) values middle)
            (.snoc (.refl _) (.walk_tail first)) good ⟨ready,available⟩
          exact (ih fuel (Nat.lt_succ_self _)).2.2.2.2.2 rest resumed.1 resumed.2.1 resumed.2.2 headSupport
    have childrenAt : ChildrenAt (width := width) fuel := by
      intro g s r e p h m c n budget inherited values before result after actual good ready available support
      cases inherited with
      | contradiction => simp only [SourceCurrentAllocatedPartialWorker.children] at actual; cases actual; exact support
      | live identity records => exact walkAt (by simpa only [SourceCurrentAllocatedPartialWorker.children] using actual) good ready available support
    have descendantsAt : DescendantsAt (width := width) fuel := by
      intro g s r e p h m c n budget inherited value before result after actual good ready resident support
      obtain ⟨combined,prefixDone,_,_,_,_⟩ := SourceCurrentEqualityOperationFixed.inherited_prefix
        value.entry.key.constraint inherited before.checked.operations good.checked.operations ready
        (good.checked.fields value.entry.key value resident)
      obtain ⟨values,middle,first,last⟩ := bind_done _ _ (by simpa only [descendants,prefixDone] using actual)
      have start := SourceCurrentOuterPrefixInvariants.reached
        (g := g) (s := s) (r := r) (e := e) (p := p) (h := h) (m := m) (c := c) (n := n) (budget := budget)
        (first := .descendants fuel inherited value before)
        (last := .children fuel combined value.children (SourceCurrentAllocatedPartialGraph.prefixState before value inherited))
        (.snoc (.refl _) (.descendants_children prefixDone)) good ⟨ready,resident⟩
      have retained := childrenAt first start.1 start.2.1 start.2.2 (by exact support)
      cases last
      exact retained
    have rowsAt : RowsAt (width := width) fuel := by
      intro g s r e p h m c n budget inherited values before result after actual good ready resident support
      cases values with
      | nil => simp only [rows] at actual; cases actual; exact support
      | cons value values =>
        cases fuel with
        | zero => simp only [rows] at actual; cases actual
        | succ fuel =>
          obtain ⟨narrowed,middle,first,later⟩ := bind_done _ _ (by simpa only [rows] using actual)
          have edgeSupport := edge_done first good ⟨ready,resident _ List.mem_cons_self⟩ support
          obtain ⟨head,afterChildren,childrenDone,last⟩ := bind_done _ _ later
          have start := SourceCurrentOuterPrefixInvariants.reached
            (g := g) (s := s) (r := r) (e := e) (p := p) (h := h) (m := m) (c := c) (n := n) (budget := budget)
            (first := .rows (fuel+1) inherited (value :: values) before)
            (last := .descendants fuel inherited narrowed middle)
            (.snoc (.refl _) (.rows_edge first)) good ⟨ready,resident⟩
          have headSupport := (ih fuel (Nat.lt_succ_self _)).2.2.2.1 childrenDone start.1 start.2.1 start.2.2 edgeSupport
          obtain ⟨tail,final,rest,done⟩ := bind_done _ _ last
          cases done
          have resumed := SourceCurrentOuterPrefixInvariants.reached
            (g := g) (s := s) (r := r) (e := e) (p := p) (h := h) (m := m) (c := c) (n := n) (budget := budget)
            (first := .rows (fuel+1) inherited (value :: values) before)
            (last := .rows fuel inherited values afterChildren)
            (.snoc (.refl _) (.rows_tail first childrenDone)) good ⟨ready,resident⟩
          exact (ih fuel (Nat.lt_succ_self _)).2.2.1 rest resumed.1 resumed.2.1 resumed.2.2 headSupport
    have bodyAt : BodyAt (width := width) fuel := by
      intro g s r e p h m c n budget request before value after actual good ready support
      cases request with
      | mk inherited original =>
        cases original with
        | empty | union => simp only [nodeBody] at actual; cases actual; exact support
        | reference name => simp only [nodeBody] at actual; cases actual
        | mu entry body depth ordinary =>
          have built := SourceCurrentMuReconstructionEffects.node_body fuel g s r e p h m c n budget
            entry body depth ordinary inherited before good.checked good.probes ready.2
          rw [built] at actual
          cases actual
          exact support
        | node entry originals depth free =>
          cases fuel with
          | zero => simp only [nodeBody] at actual; cases actual
          | succ fuel =>
            obtain ⟨rebuilt,middle,first,last⟩ := bind_done _ _ (by simpa only [nodeBody] using actual)
            have resident := resident_edges _ good.checked.heap.semantic.1.normal.facts.linked _ ready.2.resident
            have retained := (ih fuel (Nat.lt_succ_self _)).2.2.1 first good ready.1 resident support
            cases last
            exact retained
    have nodeAt : NodeAt (width := width) fuel := by
      intro g s r e p h m c n budget request before value after actual good ready support
      rcases started : beginNode request before with ⟨handle,action,running⟩
      have same := (beginNode_components request before).2.1
      rw [started] at same
      have initialSupport : Support running.merge := by rw [same]; exact support
      cases action with
      | busy | absent => simp only [nodeCall,started] at actual; cases actual
      | ready result => simp only [nodeCall,started] at actual; cases actual; exact initialSupport
      | evaluate owner =>
        obtain ⟨result,middle,body,finished⟩ := bind_done _ _ (by simpa only [nodeCall,started] using actual)
        cases finished
        have current := SourceCurrentOuterPrefixInvariants.activate started good ready
        change Support middle.merge
        exact bodyAt body current.1 current.2 initialSupport
    exact ⟨nodeAt,bodyAt,rowsAt,descendantsAt,childrenAt,walkAt⟩

private theorem node_done {fuel g s r e p h m c n budget request before value after}
    (actual : nodeCall fuel g s r e p h m c n budget request before = .done value after)
    (good : Good (width := width) before) (ready : NodeReady before request)
    (support : Support before.merge) : Support after.merge :=
  (all_done fuel).1 actual good ready support

private theorem body_done {fuel g s r e p h m c n budget request before value after}
    (actual : nodeBody fuel g s r e p h m c n budget request before = .done value after)
    (good : Good (width := width) before) (ready : NodeReady before request)
    (support : Support before.merge) : Support after.merge :=
  (all_done fuel).2.1 actual good ready support

private theorem rows_done {fuel g s r e p h m c n budget inherited values before result after}
    (actual : rows fuel g s r e p h m c n budget inherited values before = .done result after)
    (good : Good (width := width) before) (ready : EqReady before.checked.operations.constraints inherited)
    (resident : Edges before.checked.native.machine.heap values)
    (support : Support before.merge) : Support after.merge :=
  (all_done fuel).2.2.1 actual good ready resident support

private theorem descendants_done {fuel g s r e p h m c n budget inherited value before result after}
    (actual : descendants fuel g s r e p h m c n budget inherited value before = .done result after)
    (good : Good (width := width) before) (ready : EqReady before.checked.operations.constraints inherited)
    (resident : EdgeResident before.checked.native.machine.heap value)
    (support : Support before.merge) : Support after.merge :=
  (all_done fuel).2.2.2.1 actual good ready resident support

private theorem children_done {fuel g s r e p h m c n budget inherited values before result after}
    (actual : children fuel g s r e p h m c n budget inherited values before = .done result after)
    (good : Good (width := width) before) (ready : EqReady before.checked.operations.constraints inherited)
    (available : Values before.checked.native.machine.heap values)
    (support : Support before.merge) : Support after.merge :=
  (all_done fuel).2.2.2.2.1 actual good ready available support

private theorem walk_done {fuel g s r e p h m c n budget inherited index values before result after}
    (actual : walk fuel g s r e p h m c n budget inherited index values before = .done result after)
    (good : Good (width := width) before) (ready : EqReady before.checked.operations.constraints inherited)
    (available : Values before.checked.native.machine.heap values)
    (support : Support before.merge) : Support after.merge :=
  (all_done fuel).2.2.2.2.2 actual good ready available support

private theorem step_history {g s r e p h m c n budget : Nat} {first last : Phase width}
    (actual : Step g s r e p h m c n budget first last) (good : Good (caller first)) (inputs : Inputs first)
    (support : Support (caller first).merge) :
    Support (caller last).merge := by
  cases actual with
  | node_evaluate started =>
    rename_i request before handle running original fuel
    have same := (beginNode_components request before).2.1
    rw [started] at same
    change Support running.merge
    rw [same]
    exact support
  | body_rows | children_walk | walk_head | descendants_children => exact support
  | rows_edge actual => exact edge_done actual good ⟨inputs.1,inputs.2 _ List.mem_cons_self⟩ support
  | rows_tail first last =>
    have middle := SourceCurrentOuterPrefixInvariants.edge_done first good ⟨inputs.1,inputs.2 _ List.mem_cons_self⟩
    exact descendants_done last middle.1 (inputs.1.grows middle.2.1.operations.constraint_growth) middle.2.2
      (edge_done first good ⟨inputs.1,inputs.2 _ List.mem_cons_self⟩ support)
  | walk_tail actual =>
    rename_i fuel before inherited index value result middle rest
    have start := SourceCurrentOuterPrefixInvariants.reached
      (g := g) (s := s) (r := r) (e := e) (p := p) (h := h) (m := m) (c := c) (n := n) (budget := budget)
      (first := .walk (fuel+1) inherited index (value :: rest) before)
      (last := .node fuel ⟨(SourceCurrentAllocatedPartialGraph.descend before inherited index).1,value⟩
        (SourceCurrentAllocatedPartialGraph.descend before inherited index).2)
      (.snoc (.refl _) .walk_head) good inputs
    exact node_done actual start.1 start.2 (by exact support)

/-- Every actual outer prefix preserves its initial Merge support law. -/
theorem reached {g s r e p h m c n budget : Nat} {first last : Phase width}
    (actual : Reached g s r e p h m c n budget first last) (good : Good (caller first)) (inputs : Inputs first)
    (support : Support (caller first).merge) :
    Support (caller last).merge := by
  induction actual with
  | refl => exact support
  | snoc earlier last ih =>
    have current := SourceCurrentOuterPrefixInvariants.reached earlier good inputs
    exact step_history last current.1 current.2 ih

private theorem busy {g s r e p h m c n budget handle : Nat} {phase : Phase width} {after : Caller width}
    (good : Good (caller phase)) (inputs : Inputs phase)
    (support : Support (caller phase).merge)
    (actual : SourceCurrentOuterActiveAncestry.run g s r e p h m c n budget phase = .failed (.nodeMemo handle .busy) after) :
    Support after.merge := by
  obtain ⟨_,fuel,request,past,_⟩ := SourceCurrentOuterPrefixInvariants.busy good inputs actual
  exact reached past good inputs support

private theorem initial_node {fuel g s r e p h m c n budget request checked fourth value after}
    (actual : nodeCall fuel g s r e p h m c n budget request
      (initial checked SourceCurrentMemoMergeGraph.empty fourth) = .done value after)
    (good : SourceCurrentNativeOperationHeap.Good (width := width) checked)
    (probes : InternedFreshOrdinaryProbeHeap.Heap checked.native.machine.heap)
    (ready : NodeReady (initial checked SourceCurrentMemoMergeGraph.empty fourth) request) :
    Support after.merge :=
  node_done actual (SourceCurrentOuterPrefixInvariants.initial _ _ _ good
    (SourceCurrentMemoMergeEffects.stored_empty _) probes) ready SourceCurrentMergePositivePosition.support_empty

/-- An outer prefix from empty Merge tables derives the support law without a future return. -/
theorem initial_reached {fuel g s r e p h m c n budget request checked fourth last}
    (actual : Reached g s r e p h m c n budget
      (.node fuel request (initial checked SourceCurrentMemoMergeGraph.empty fourth)) last)
    (good : SourceCurrentNativeOperationHeap.Good (width := width) checked)
    (probes : InternedFreshOrdinaryProbeHeap.Heap checked.native.machine.heap)
    (ready : NodeReady (initial checked SourceCurrentMemoMergeGraph.empty fourth) request) :
    Support (caller last).merge :=
  reached actual (SourceCurrentOuterPrefixInvariants.initial _ _ _ good
    (SourceCurrentMemoMergeEffects.stored_empty _) probes) ready SourceCurrentMergePositivePosition.support_empty

end MicroCFTA.SourceCurrentOuterMergePositionSupport
