import MicroCFTA.SourceCurrentLowerOperationInvariants
import MicroCFTA.SourceCurrentNativeGuardHeapReturns
import MicroCFTA.SourceCurrentConstrainedCapProjectionGuard
import MicroCFTA.SourceCurrentConstrainedCapMergeJointEffects

/-!
# Causal guard heaps through actual lower-worker returns

Each successful worker uses its actual intermediate physical states.
Initial physical invariants supply availability and semantic readiness.
The result retains arbitrary-predicate Mu guard observations. It does not
assert a predicate for every returned raw guard or establish completion.
-/
namespace MicroCFTA.SourceCurrentLowerGuardHeapReturns
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
local notation "Edge" => EdgeValue Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Shared" => SourceCurrentAllocatedSharedTargetState.State
local notation "FieldAvailable" => SourceCurrentConjunctionEquality.FieldAvailable
local notation "Heap" => SourceCurrentConstrainedCapGuardHeap.Heap
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

private theorem shared_head [DecidableEq (EdgeKey Symbol Guard)] (annotation : Guard → Prop) {h value before result after}
    (actual : SourceCurrentAllocatedSharedEditWorker.head h value before = .done result after)
    (good : SharedGood (width := width) before) (available : Available before.checked.native.machine.heap value)
    (heap : Heap annotation before.checked.native.machine.heap) :
    Effect before.checked after.checked ∧ SharedGood after ∧ Available after.checked.native.machine.heap result ∧
      Heap annotation after.checked.native.machine.heap := by
  cases returned : SourceEqualityRequiredWorker.head h value before.checked.native.machine.heap with
  | pending | unresolved | exhausted => simp only [SourceCurrentAllocatedSharedEditWorker.head,returned] at actual; cases actual
  | done output heapAfter =>
    simp only [SourceCurrentAllocatedSharedEditWorker.head,returned] at actual
    cases actual
    have graph := SourceEqualityRequiredWorkerSound.head_graph h value _ _ heapAfter returned
    obtain ⟨keeps,semantic,costs,fields,known⟩ := SourceCurrentRequiredHeapEffects.head
      (FieldAvailable before.checked.operations) graph good.checked.semantic good.checked.costs good.checked.fields available
    have effect := same_operations good.checked heapAfter keeps semantic costs fields
    exact ⟨effect,shared_advance good effect,known,
      SourceCurrentConstrainedCapProjectionGuard.head annotation graph good.checked.semantic good.checked.costs available heap⟩

private theorem projection [DecidableEq (EdgeKey Symbol Guard)] (annotation : Guard → Prop) {p h path values before memo result after saved}
    (actual : SourceCurrentAllocatedTargetWorker.projection p h path values before memo = .done result after saved)
    (good : Good (width := width) before) (available : Values before.native.machine.heap values)
    (heap : Heap annotation before.native.machine.heap) : Heap annotation after.native.machine.heap := by
  obtain ⟨heapAfter,graph,rfl,rfl⟩ := SourceCurrentAllocatedTargetWorkerSound.projection_sound p h path values before memo result after saved actual
  exact SourceCurrentConstrainedCapProjectionGuard.forest annotation graph good.semantic good.costs available heap

private theorem merge [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (annotation : Guard → Prop) {m s input before memo result after saved}
    (actual : SourceCurrentAllocatedTargetWorker.merge m s input before memo = .done result after saved)
    (good : Good (width := width) before) (stored : Stored before.native.machine.heap memo)
    (available : Available before.native.machine.heap input) (heap : Heap annotation before.native.machine.heap) :
    Heap annotation after.native.machine.heap := by
  have graph := SourceCurrentAllocatedTargetWorkerSound.merge_sound m s input before memo result after saved actual
  cases graph with
  | done call =>
    exact SourceCurrentConstrainedCapMergeJointEffects.call_heap annotation call.graph good.semantic good.costs stored available heap

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A completed operand retains causal guard observations through its own projection and Merge. -/
theorem operand (annotation : Guard → Prop) {p h m s path values before memo result after saved}
    (actual : SourceCurrentAllocatedTargetWorker.operand p h m s path values before memo = .done result after saved)
    (good : Good (width := width) before) (stored : Stored before.native.machine.heap memo)
    (available : Values before.native.machine.heap values) (heap : Heap annotation before.native.machine.heap) :
    Heap annotation after.native.machine.heap := by
  obtain ⟨value,middle,current,first,last⟩ := (SourceCurrentAllocatedTargetWorkerSound.bind_done _ _ result after saved).mp actual
  obtain ⟨heapAfter,graph,rfl,rfl⟩ := SourceCurrentAllocatedTargetWorkerSound.projection_sound p h path values before memo value middle current first
  have checked := SourceEqualityProjectionCosts.forest_effects graph good.semantic good.costs available
  have fields := SourceCurrentOpenProjectionFields.forest (FieldAvailable before.operations) graph good.semantic good.costs available good.fields
  have effect := same_operations good heapAfter checked.1 checked.2.1 checked.2.2.1 fields
  exact merge annotation last effect.good (stored.grows effect.keeps) checked.2.2.2
    (projection annotation first good available heap)

private theorem query (annotation : Guard → Prop) {n left right before result after}
    (actual : SourceEqualityNativeDemand.execute n
      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) before = .done result after)
    (good : Good (width := width) before) (first : Available before.native.machine.heap left)
    (second : Available before.native.machine.heap right) (heap : Heap annotation before.native.machine.heap) :
    Heap annotation after.native.machine.heap :=
  SourceCurrentNativeGuardHeapReturns.node annotation n ⟨IntersectionEmptyDomain.emptyDomain,left,right⟩ before after result good heap
    ⟨SourceRecursiveIntersectionKernel.empty_domain _,first,second⟩ actual

private theorem target_leaf (annotation : Guard → Prop) {n left right before memo result after saved}
    (actual : SourceCurrentAllocatedTargetWorker.leaf n left right before memo = .done result after saved)
    (good : Good (width := width) before) (first : Available before.native.machine.heap left)
    (second : Available before.native.machine.heap right) (heap : Heap annotation before.native.machine.heap) :
    Heap annotation after.native.machine.heap := by
  cases observed : SourceEqualityNativeDemand.execute n
      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) before with
  | done value checked =>
    simp only [SourceCurrentAllocatedTargetWorker.leaf,observed] at actual
    cases actual
    exact query annotation observed good first second heap
  | yielded | failed | constraintError | blocked => simp only [SourceCurrentAllocatedTargetWorker.leaf,observed] at actual; cases actual

private theorem target_fold (annotation : Guard → Prop) {p h m s n values seed paths before memo result after saved}
    (actual : SourceCurrentAllocatedTargetWorker.fold p h m s n values seed paths before memo = .done result after saved)
    (good : Good (width := width) before) (stored : Stored before.native.machine.heap memo)
    (available : Values before.native.machine.heap values) (heap : Heap annotation before.native.machine.heap) :
    Heap annotation after.native.machine.heap := by
  induction paths generalizing before memo result after saved with
  | nil => exact operand annotation actual good stored available heap
  | cons path paths ih =>
    obtain ⟨head,middle,current,first,later⟩ := (SourceCurrentAllocatedTargetWorkerSound.bind_done _ _ result after saved).mp actual
    obtain ⟨headEffect,headStored,headAvailable⟩ := SourceCurrentLowerOperationInvariants.operand first good stored available
    have firstHeap := operand annotation first good stored available heap
    obtain ⟨tail,final,completed,rest,last⟩ := (SourceCurrentAllocatedTargetWorkerSound.bind_done _ _ result after saved).mp later
    have laterAvailable := fun value member => headEffect.keeps.available value (available value member)
    obtain ⟨tailEffect,tailStored,tailAvailable⟩ := SourceCurrentLowerOperationInvariants.target (paths := seed :: paths) rest headEffect.good headStored laterAvailable
    have tailHeap := ih rest headEffect.good headStored laterAvailable firstHeap
    exact target_leaf annotation last tailEffect.good (tailEffect.keeps.available _ headAvailable) tailAvailable tailHeap

/-- A completed literal target retains the initial causal guard heap through its ordered queries. -/
theorem target (annotation : Guard → Prop) {p h m s n values paths before memo result after saved}
    (actual : SourceCurrentAllocatedTargetWorker.target p h m s n values paths before memo = .done result after saved)
    (good : Good (width := width) before) (stored : Stored before.native.machine.heap memo)
    (available : Values before.native.machine.heap values) (heap : Heap annotation before.native.machine.heap) :
    Heap annotation after.native.machine.heap := by
  cases paths with
  | nil => cases actual; exact heap
  | cons seed paths => exact target_fold annotation actual good stored available heap

/-- Both an actual target slot hit and a constructed miss retain causal guard profiles. -/
theorem force (annotation : Guard → Prop) {p h m s n record originals path before result after}
    (actual : SourceCurrentAllocatedSharedTargetWorker.force p h m s n record originals path before = .done result after)
    (good : SharedGood (width := width) before) (available : Values before.checked.native.machine.heap originals)
    (heap : Heap annotation before.checked.native.machine.heap) : Heap annotation after.checked.native.machine.heap := by
  cases found : before.targets path with
  | some value => simp only [SourceCurrentAllocatedSharedTargetWorker.force,found] at actual; cases actual; exact heap
  | none =>
    cases returned : SourceCurrentAllocatedTargetWorker.target p h m s n originals
        (SourceEqualityClassTarget.operandPaths record.paths path) before.checked before.memo with
    | failed => simp only [SourceCurrentAllocatedSharedTargetWorker.force,found,returned] at actual; cases actual
    | done value checked saved =>
      simp only [SourceCurrentAllocatedSharedTargetWorker.force,found,returned] at actual
      cases actual
      exact target annotation returned good.checked good.stored available heap

/-- A completed shared leaf retains the guard heap produced by its actual force and native call. -/
theorem leaf (annotation : Guard → Prop) {p h m s n record originals path input before result after}
    (actual : SourceCurrentAllocatedSharedTargetWorker.leaf p h m s n record originals path input before = .done result after)
    (good : SharedGood (width := width) before) (originalsAvailable : Values before.checked.native.machine.heap originals)
    (available : Available before.checked.native.machine.heap input) (heap : Heap annotation before.checked.native.machine.heap) :
    Heap annotation after.checked.native.machine.heap := by
  cases first : SourceCurrentAllocatedSharedTargetWorker.force p h m s n record originals path before with
  | failed => simp only [SourceCurrentAllocatedSharedTargetWorker.leaf,first,SourceCurrentAllocatedSharedTargetWorker.Outcome.bind] at actual; cases actual
  | done value middle =>
    simp only [SourceCurrentAllocatedSharedTargetWorker.leaf,first,SourceCurrentAllocatedSharedTargetWorker.Outcome.bind] at actual
    obtain ⟨firstEffect,current,known⟩ := SourceCurrentLowerOperationInvariants.force first good originalsAvailable
    have forced := force annotation first good originalsAvailable heap
    cases last : SourceEqualityNativeDemand.execute n
        (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain value input)) middle.checked with
    | yielded | failed | constraintError | blocked => simp only [SourceCurrentAllocatedSharedTargetWorker.step,last] at actual; cases actual
    | done output checked =>
      simp only [SourceCurrentAllocatedSharedTargetWorker.step,last] at actual
      cases actual
      exact query annotation last current.checked known (firstEffect.keeps.available input available) forced

private def ChildContract (annotation : Guard → Prop) (record : SourceEqualityClassOrder.Record)
    (originals : List Node) (e p h m s n : Nat) : Prop :=
  ∀ (edits : SourceEqualityEdits.Edits EqualityNormalize.Path) (value : Node) (before : Shared width) (output : Node) (after : Shared width),
    SourceCurrentAllocatedSharedEditWorker.edit record originals e p h m s n edits value before = .done output after →
    SharedGood before → Values before.checked.native.machine.heap originals → Available before.checked.native.machine.heap value →
    Heap annotation before.checked.native.machine.heap → Heap annotation after.checked.native.machine.heap

private theorem edit_children (annotation : Guard → Prop) {record originals e p h m s n}
    (child : ChildContract annotation record originals e p h m s n) {entries index values before results after}
    (actual : SourceCurrentAllocatedSharedEditWorker.children
      (SourceCurrentAllocatedSharedEditWorker.edit record originals e p h m s n) entries index values before = .done results after)
    (good : SharedGood (width := width) before) (originalsAvailable : Values before.checked.native.machine.heap originals)
    (available : Values before.checked.native.machine.heap values) (heap : Heap annotation before.checked.native.machine.heap) :
    Heap annotation after.checked.native.machine.heap := by
  induction values generalizing index before results after with
  | nil => cases actual; exact heap
  | cons value values ih =>
    cases found : SourceEqualityNeededMap.lookup (index : Int) entries with
    | none =>
      simp only [SourceCurrentAllocatedSharedEditWorker.children,found] at actual
      obtain ⟨tail,final,rest,returned⟩ := shared_bind_done _ _ actual
      cases returned
      exact ih rest good originalsAvailable (fun value member => available value (List.mem_cons_of_mem _ member)) heap
    | some edits =>
      simp only [SourceCurrentAllocatedSharedEditWorker.children,found] at actual
      obtain ⟨result,middle,first,later⟩ := shared_bind_done _ _ actual
      obtain ⟨tail,final,rest,returned⟩ := shared_bind_done _ _ later
      cases returned
      obtain ⟨effect,current,known⟩ := SourceCurrentLowerOperationInvariants.edit first good originalsAvailable (available _ List.mem_cons_self)
      exact ih rest current (fun value member => effect.keeps.available value (originalsAvailable value member))
        (fun value member => effect.keeps.available value (available value (List.mem_cons_of_mem _ member)))
        (child edits value before result middle first good originalsAvailable (available _ List.mem_cons_self) heap)

private theorem edit_rows (annotation : Guard → Prop) {record originals e p h m s n}
    (child : ChildContract annotation record originals e p h m s n) {entries rows before results after}
    (actual : SourceCurrentAllocatedSharedEditWorker.rows
      (SourceCurrentAllocatedSharedEditWorker.edit record originals e p h m s n) entries rows before = .done results after)
    (good : SharedGood (width := width) before) (originalsAvailable : Values before.checked.native.machine.heap originals)
    (resident : Edges before.checked.native.machine.heap rows) (heap : Heap annotation before.checked.native.machine.heap) :
    Heap annotation after.checked.native.machine.heap := by
  induction rows generalizing before results after with
  | nil => cases actual; exact heap
  | cons edge rows ih =>
    obtain ⟨values,middle,children,later⟩ := shared_bind_done _ _ actual
    have available := good.checked.heap.semantic.1.normal.facts.cached.edges _ _ (resident _ List.mem_cons_self)
    have childrenActual : SourceCurrentAllocatedSharedEditWorker.editList
        (SourceCurrentAllocatedSharedEditWorker.edit record originals e p h m s n)
        (.editBelow entries) edge.children before = .done values middle := children
    obtain ⟨firstEffect,current,known⟩ := SourceCurrentLowerOperationInvariants.edit_list childrenActual good originalsAvailable available
    have firstHeap := edit_children annotation child children good originalsAvailable available heap
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
      (fun edge member => edge_grows _ _ prefixEffect.keeps.growth edge (resident edge (List.mem_cons_of_mem _ member))) firstHeap

/-- Literal edit recursion retains arbitrary-predicate causal Mu observations without reached-input certificates. -/
theorem edit (annotation : Guard → Prop) {record originals e p h m s n edits value before result after}
    (actual : SourceCurrentAllocatedSharedEditWorker.edit record originals e p h m s n edits value before = .done result after)
    (good : SharedGood (width := width) before) (originalsAvailable : Values before.checked.native.machine.heap originals)
    (available : Available before.checked.native.machine.heap value) (heap : Heap annotation before.checked.native.machine.heap) :
    Heap annotation after.checked.native.machine.heap := by
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
        exact leaf annotation observed good originalsAvailable available heap
    | editBelow entries =>
      cases value with
      | empty => cases actual; exact heap
      | reference => cases actual
      | node entry rows depth free =>
        obtain ⟨rebuilt,middle,first,last⟩ := shared_bind_done _ _ actual
        have resident := resident_edges _ good.checked.heap.semantic.1.normal.facts.linked _ available.resident
        have guarded := edit_rows annotation (fun _ _ _ _ _ => ih) first good originalsAvailable resident heap
        simp only [SourceCurrentAllocatedSharedEditWorker.work] at last
        cases last
        exact SourceCurrentConstrainedCapGuardHeap.preserve annotation _ _ guarded (InternedShallowHeap.makeNode_noNewMu rebuilt _)
      | mu | union =>
        obtain ⟨exposed,middle,first,last⟩ := shared_bind_done _ _ actual
        obtain ⟨effect,current,known,guarded⟩ := shared_head annotation first good available heap
        exact ih last current (fun value member => effect.keeps.available value (originalsAvailable value member)) known guarded

/-- A completed class edit list retains causal guard observations in its exact returned shared state. -/
theorem edit_list (annotation : Guard → Prop) {record originals e p h m s n edits values before results after}
    (actual : SourceCurrentAllocatedSharedEditWorker.editList
      (SourceCurrentAllocatedSharedEditWorker.edit record originals e p h m s n) edits values before = .done results after)
    (good : SharedGood (width := width) before) (originalsAvailable : Values before.checked.native.machine.heap originals)
    (available : Values before.checked.native.machine.heap values) (heap : Heap annotation before.checked.native.machine.heap) :
    Heap annotation after.checked.native.machine.heap := by
  cases edits with
  | editAt => cases actual; exact heap
  | editBelow entries => exact edit_children annotation (fun _ _ _ _ _ => edit annotation) actual good originalsAvailable available heap

/-- A completed class derives guard-heap retention from its actual freshly initialized edit run. -/
theorem run_class (annotation : Guard → Prop) {e p h m s n record values before memo results after saved}
    (actual : SourceCurrentAllocatedClassWorker.runClass e p h m s n record values before memo = .done results after saved)
    (good : Good (width := width) before) (stored : Stored before.native.machine.heap memo)
    (available : Values before.native.machine.heap values) (heap : Heap annotation before.native.machine.heap) :
    Heap annotation after.native.machine.heap := by
  cases returned : SourceCurrentAllocatedSharedEditWorker.editList
      (SourceCurrentAllocatedSharedEditWorker.edit record values e p h m s n)
      (SourceCurrentAllocatedClassEditPlan.compiled record) values (SourceCurrentAllocatedSharedTargetState.initial before memo) with
  | failed => simp only [SourceCurrentAllocatedClassWorker.runClass,returned] at actual; cases actual
  | done output shared =>
    simp only [SourceCurrentAllocatedClassWorker.runClass,returned] at actual
    cases actual
    exact edit_list annotation returned (SharedGood.initial good stored) available available heap

/-- The literal right fold retains causal guard observations through its actual tail and head calls. -/
theorem class_fold (annotation : Guard → Prop) {e p h m s n records values before memo results after saved}
    (actual : SourceCurrentAllocatedClassWorker.fold e p h m s n records values before memo = .done results after saved)
    (good : Good (width := width) before) (stored : Stored before.native.machine.heap memo)
    (available : Values before.native.machine.heap values) (heap : Heap annotation before.native.machine.heap) :
    Heap annotation after.native.machine.heap := by
  induction records generalizing values before memo results after saved with
  | nil => cases actual; exact heap
  | cons record records ih =>
    obtain ⟨middle,checked,current,first,last⟩ := class_bind_done _ _ actual
    obtain ⟨effect,retained,known⟩ := SourceCurrentLowerOperationInvariants.class_fold first good stored available
    exact run_class annotation last effect.good retained known (ih first good stored available heap)

/-- Propagating the final class results changes no constructor heap or guard observation. -/
theorem class_pass (annotation : Guard → Prop) {e p h m s n records values before memo results after saved}
    (actual : SourceCurrentAllocatedClassWorker.pass e p h m s n records values before memo = .done results after saved)
    (good : Good (width := width) before) (stored : Stored before.native.machine.heap memo)
    (available : Values before.native.machine.heap values) (heap : Heap annotation before.native.machine.heap) :
    Heap annotation after.native.machine.heap := by
  obtain ⟨middle,checked,current,first,last⟩ := class_bind_done _ _ actual
  cases last
  exact class_fold annotation first good stored available heap

end MicroCFTA.SourceCurrentLowerGuardHeapReturns
