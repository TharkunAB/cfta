import MicroCFTA.SourceCurrentNativeOperationHeap
import MicroCFTA.SourceCurrentOpenProjectionFields
import MicroCFTA.SourceCurrentAllocatedParentWorker
import MicroCFTA.SourceCurrentAllocatedTargetWorkerSound
import MicroCFTA.SourceCurrentAllocatedMergePhysical
import MicroCFTA.SourceCurrentConjunctionCallUnique
import MicroCFTA.SourceCurrentConjunctionWorkerCompletion

/-!
# Physical invariants through actual completed lower workers

The proofs inspect literal successful worker equations. Initial physical
memo entries must contain available results. No reached range, input plan,
semantic native result law, or supplied completed graph is an input.
-/
namespace MicroCFTA.SourceCurrentLowerOperationInvariants
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentNativeOperationHeap (Good)
open SourceCurrentMemoMergeEffects (Stored)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Shared" => SourceCurrentAllocatedSharedTargetState.State
local notation "Record" => SourceEqualityClassOrder.Record
local notation "Fields" => SourceCurrentConjunctionEquality.Fields
local notation "FieldAvailable" => SourceCurrentConjunctionEquality.FieldAvailable
local notation "Effects" => SourceCurrentConjunctionRowsAllocation.Effects
variable {width : Nat}

/-- Initial probe heaps and weak native cells provide the physical lower-worker state. -/
theorem _root_.MicroCFTA.SourceCurrentNativeOperationHeap.Good.physical {before : Checked width} (good : Good before) :
    SourceCurrentConjunctionRowsAllocation.Ready (physical before) :=
  ⟨good.semantic,good.costs,good.operations,good.fields⟩

/-- Literal physical advancement retains all weak native cells and full equality memo validity. -/
theorem _root_.MicroCFTA.SourceCurrentNativeOperationHeap.Good.advance {before : Checked width} (good : Good before) (after : Physical)
    (effects : Effects (physical before) after) : Good (advancePhysical before after) := by
  have extension := SourceCurrentAllocatedQueryMemo.advance_extension before after effects
  have valid : SourceRecursiveIntersectionKernel.Valid (advancePhysical before after).native.machine :=
    ⟨effects.ready.semantic.ready.semantic.1.normal.facts,good.native.machine.2⟩
  exact ⟨⟨valid,
    FlatMemoThunk.Valid.map _ _ _ _ good.native.nodes (fun _ ready => ready.grows extension),
    FlatMemoThunk.Valid.map _ _ _ _ good.native.edges (fun _ ready => ready.grows extension)⟩,
    effects.keeps.ready,effects.ready.valid,effects.ready.fields,effects.ready.semantic,effects.ready.costs⟩

/-- A successful stage retains the exact current heap and all earlier physical records. -/
structure Effect (before after : Checked width) : Prop where
  /-- Every final physical invariant follows from the initial state. -/
  good : Good after
  /-- Constructor records and issued identities remain present. -/
  keeps : SourceEqualityRequiredCache.Keeps before.native.machine.heap after.native.machine.heap
  /-- Equality allocation and completed operation entries grow. -/
  operations : SourceEqualityConstraintMemoAllocation.Grows before.operations after.operations

/-- An unchanged checked state retains all initial invariants. -/
theorem Effect.refl (before : Checked width) (good : Good before) : Effect before before :=
  ⟨good,SourceEqualityRequiredCache.pure_keeps _ good.heap,SourceEqualityConstraintMemoAllocation.grows_refl _⟩

/-- Consecutive actual returns retain both physical histories. -/
theorem Effect.trans {before middle after : Checked width} (first : Effect before middle)
    (last : Effect middle after) : Effect before after :=
  ⟨last.good,first.keeps.trans last.keeps,SourceCurrentConjunctionEquality.grows_trans first.operations last.operations⟩

private theorem advanced {before : Checked width} (good : Good before) {after : Physical}
    (effects : Effects (physical before) after) : Effect before (advancePhysical before after) :=
  ⟨good.advance after effects,effects.keeps,effects.grows⟩

private theorem same_operations {before : Checked width} (good : Good before)
    (heap : State Symbol Guard) (keeps : SourceEqualityRequiredCache.Keeps before.native.machine.heap heap)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady heap)
    (costs : InternedFreshOrdinaryCostHeap.Heap heap) (fields : Fields before.operations heap) :
    Effect before (advancePhysical before ⟨heap,before.operations⟩) :=
  advanced good ⟨keeps,⟨semantic,costs,good.operations,fields⟩,SourceEqualityConstraintMemoAllocation.grows_refl _⟩

private theorem forest {path values before result heap}
    [DecidableEq (EdgeKey Symbol Guard)]
    (actual : SourceEqualityProjectionGraph.Forest path values before.native.machine.heap result heap)
    (good : Good (width := width) before) (available : Values before.native.machine.heap values) :
    Effect before (advancePhysical before ⟨heap,before.operations⟩) ∧ Available heap result := by
  have checked := SourceEqualityProjectionCosts.forest_effects actual good.semantic good.costs available
  have fields := SourceCurrentOpenProjectionFields.forest (FieldAvailable before.operations)
    actual good.semantic good.costs available good.fields
  exact ⟨same_operations good heap checked.1 checked.2.1 checked.2.2.1 fields,checked.2.2.2⟩

private theorem projection {p h path values before memo result after saved}
    [DecidableEq (EdgeKey Symbol Guard)]
    (actual : SourceCurrentAllocatedTargetWorker.projection p h path values before memo = .done result after saved)
    (good : Good (width := width) before) (available : Values before.native.machine.heap values) :
    Effect before after ∧ Available after.native.machine.heap result ∧ saved = memo := by
  obtain ⟨heap,graph,rfl,rfl⟩ := SourceCurrentAllocatedTargetWorkerSound.projection_sound p h path values before memo result after saved actual
  exact ⟨(forest graph good available).1,(forest graph good available).2,rfl⟩

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem merge {m s input before memo result after saved}
    (actual : SourceCurrentAllocatedTargetWorker.merge m s input before memo = .done result after saved)
    (good : Good (width := width) before) (stored : Stored before.native.machine.heap memo)
    (available : Available before.native.machine.heap input) :
    Effect before after ∧ Stored after.native.machine.heap saved ∧ Available after.native.machine.heap result := by
  have graph := SourceCurrentAllocatedTargetWorkerSound.merge_sound m s input before memo result after saved actual
  cases graph with
  | done call =>
    obtain ⟨effects,stored,available,_⟩ := call.verified good.physical stored available
    exact ⟨advanced good effects,stored,available⟩

/-- Completed operands derive every actual projection and allocated merge invariant. -/
theorem operand {p h m s path values before memo result after saved}
    (actual : SourceCurrentAllocatedTargetWorker.operand p h m s path values before memo = .done result after saved)
    (good : Good (width := width) before) (stored : Stored before.native.machine.heap memo)
    (available : Values before.native.machine.heap values) :
    Effect before after ∧ Stored after.native.machine.heap saved ∧ Available after.native.machine.heap result := by
  obtain ⟨value,middle,current,first,last⟩ := (SourceCurrentAllocatedTargetWorkerSound.bind_done _ _ result after saved).mp actual
  obtain ⟨effect,known,rfl⟩ := projection first good available
  obtain ⟨remaining,retained,returned⟩ := merge last effect.good (stored.grows effect.keeps) known
  exact ⟨effect.trans remaining,retained,returned⟩

private theorem query {n left right before result after}
    (actual : SourceEqualityNativeDemand.execute n
      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) before = .done result after)
    (good : Good (width := width) before) (first : Available before.native.machine.heap left)
    (second : Available before.native.machine.heap right) : Effect before after ∧ Available after.native.machine.heap result := by
  have ready : SourceRecursiveIntersectionThunks.NodeReady before.native.machine
      ⟨IntersectionEmptyDomain.emptyDomain,left,right⟩ := ⟨SourceRecursiveIntersectionKernel.empty_domain before.native.machine,first,second⟩
  obtain ⟨final,_,keeps,growth,available⟩ := SourceCurrentNativeOperationHeap.node n _ before after result good ready actual
  exact ⟨⟨final,keeps,growth⟩,available⟩

private theorem target_leaf {n left right before memo result after saved}
    (actual : SourceCurrentAllocatedTargetWorker.leaf n left right before memo = .done result after saved)
    (good : Good (width := width) before) (first : Available before.native.machine.heap left)
    (second : Available before.native.machine.heap right) :
    Effect before after ∧ Available after.native.machine.heap result ∧ saved = memo := by
  cases observed : SourceEqualityNativeDemand.execute n
      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) before with
  | done value checked =>
    simp only [SourceCurrentAllocatedTargetWorker.leaf,observed] at actual
    cases actual
    exact ⟨(query observed good first second).1,(query observed good first second).2,rfl⟩
  | yielded | failed | constraintError | blocked => simp only [SourceCurrentAllocatedTargetWorker.leaf,observed] at actual; cases actual

private theorem target_fold {p h m s n values seed paths before memo result after saved}
    (actual : SourceCurrentAllocatedTargetWorker.fold p h m s n values seed paths before memo = .done result after saved)
    (good : Good (width := width) before) (stored : Stored before.native.machine.heap memo)
    (available : Values before.native.machine.heap values) :
    Effect before after ∧ Stored after.native.machine.heap saved ∧ Available after.native.machine.heap result := by
  induction paths generalizing before memo result after saved with
  | nil => exact operand actual good stored available
  | cons path paths ih =>
    obtain ⟨head,middle,current,first,later⟩ := (SourceCurrentAllocatedTargetWorkerSound.bind_done _ _ result after saved).mp actual
    obtain ⟨headEffect,headStored,headAvailable⟩ := operand first good stored available
    obtain ⟨tail,final,completed,rest,last⟩ := (SourceCurrentAllocatedTargetWorkerSound.bind_done _ _ result after saved).mp later
    obtain ⟨tailEffect,tailStored,tailAvailable⟩ := ih rest headEffect.good headStored
      (fun value member => headEffect.keeps.available value (available value member))
    obtain ⟨lastEffect,lastAvailable,rfl⟩ := target_leaf last tailEffect.good
      (tailEffect.keeps.available _ headAvailable) tailAvailable
    exact ⟨(headEffect.trans tailEffect).trans lastEffect,tailStored.grows lastEffect.keeps,lastAvailable⟩

/-- Every completed target derives full physical validity from its initial forest and merge entries. -/
theorem target {p h m s n values paths before memo result after saved}
    (actual : SourceCurrentAllocatedTargetWorker.target p h m s n values paths before memo = .done result after saved)
    (good : Good (width := width) before) (stored : Stored before.native.machine.heap memo)
    (available : Values before.native.machine.heap values) :
    Effect before after ∧ Stored after.native.machine.heap saved ∧ Available after.native.machine.heap result := by
  cases paths with
  | nil => cases actual; exact ⟨.refl _ good,stored,empty_available _⟩
  | cons seed paths => exact target_fold actual good stored available

/-- Warm target slots need only physical residency for this invariant proof. -/
structure SharedGood (state : Shared width) : Prop where
  /-- The checked state retains full physical invariants. -/
  checked : Good state.checked
  /-- Warm merge entries retain their available original and returned values. -/
  stored : Stored state.checked.native.machine.heap state.memo
  /-- Every installed target is available at the current heap. -/
  slots : ∀ path value, state.targets path = some value → Available state.checked.native.machine.heap value

/-- A new class starts with no slot assumptions. -/
omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
theorem SharedGood.initial {before : Checked width} {memo : Memo}
    (good : Good before) (stored : Stored before.native.machine.heap memo) :
    SharedGood (SourceCurrentAllocatedSharedTargetState.initial before memo) :=
  ⟨good,stored,by intro _ _ impossible; cases impossible⟩

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem shared_advance {before : Shared width} (good : SharedGood before) {checked : Checked width}
    (effect : Effect before.checked checked) :
    SharedGood (SourceCurrentAllocatedSharedTargetState.advance before checked) :=
  ⟨effect.good,good.stored.grows effect.keeps,
    fun path value present => effect.keeps.available value (good.slots path value present)⟩

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem shared_bind_done {A B : Type}
    (first : SourceCurrentAllocatedSharedEditWorker.Outcome width A)
    (next : A → Shared width → SourceCurrentAllocatedSharedEditWorker.Outcome width B)
    {output : B} {after : Shared width} (actual : first.bind next = .done output after) :
    ∃ value middle, first = .done value middle ∧ next value middle = .done output after := by
  cases first with
  | done value middle => exact ⟨value,middle,rfl,actual⟩
  | failed => cases actual

/-- A completed slot hit or target miss derives the current available winner and physical tables. -/
theorem force {p h m s n record originals path before result after}
    (actual : SourceCurrentAllocatedSharedTargetWorker.force p h m s n record originals path before = .done result after)
    (good : SharedGood (width := width) before) (available : Values before.checked.native.machine.heap originals) :
    Effect before.checked after.checked ∧ SharedGood after ∧ Available after.checked.native.machine.heap result := by
  cases found : before.targets path with
  | some value =>
    simp only [SourceCurrentAllocatedSharedTargetWorker.force,found] at actual
    cases actual
    exact ⟨.refl _ good.checked,good,good.slots path _ found⟩
  | none =>
    cases returned : SourceCurrentAllocatedTargetWorker.target p h m s n originals
        (SourceEqualityClassTarget.operandPaths record.paths path) before.checked before.memo with
    | failed => simp only [SourceCurrentAllocatedSharedTargetWorker.force,found,returned] at actual; cases actual
    | done value checked saved =>
      simp only [SourceCurrentAllocatedSharedTargetWorker.force,found,returned] at actual
      cases actual
      obtain ⟨effect,stored,known⟩ := target returned good.checked good.stored available
      refine ⟨effect,⟨effect.good,stored,?_⟩,known⟩
      intro key output present
      dsimp only [SourceCurrentAllocatedSharedTargetState.store,put] at present
      split at present
      · cases Option.some.inj present; exact known
      · exact effect.keeps.available output (good.slots key output present)

/-- A completed shared leaf derives its actual native result after the same force return. -/
theorem leaf {p h m s n record originals path input before result after}
    (actual : SourceCurrentAllocatedSharedTargetWorker.leaf p h m s n record originals path input before = .done result after)
    (good : SharedGood (width := width) before) (originalsAvailable : Values before.checked.native.machine.heap originals)
    (available : Available before.checked.native.machine.heap input) :
    Effect before.checked after.checked ∧ SharedGood after ∧ Available after.checked.native.machine.heap result := by
  cases first : SourceCurrentAllocatedSharedTargetWorker.force p h m s n record originals path before with
  | failed => simp only [SourceCurrentAllocatedSharedTargetWorker.leaf,first,SourceCurrentAllocatedSharedTargetWorker.Outcome.bind] at actual; cases actual
  | done value middle =>
    simp only [SourceCurrentAllocatedSharedTargetWorker.leaf,first,SourceCurrentAllocatedSharedTargetWorker.Outcome.bind] at actual
    obtain ⟨firstEffect,current,known⟩ := force first good originalsAvailable
    cases last : SourceEqualityNativeDemand.execute n
        (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain value input)) middle.checked with
    | yielded | failed | constraintError | blocked => simp only [SourceCurrentAllocatedSharedTargetWorker.step,last] at actual; cases actual
    | done output checked =>
      simp only [SourceCurrentAllocatedSharedTargetWorker.step,last] at actual
      cases actual
      obtain ⟨effect,known⟩ := query last current.checked known (firstEffect.keeps.available input available)
      exact ⟨firstEffect.trans effect,shared_advance current effect,known⟩

omit [DecidableEq Symbol] in
private theorem node_constructor {before : Checked width} (good : Good before) (rows : List Edge)
    (resident : Edges before.native.machine.heap rows) :
    Effect before (advancePhysical before ⟨(run (makeNode rows) before.native.machine.heap).2,before.operations⟩) ∧
      Available (run (makeNode rows) before.native.machine.heap).2 (run (makeNode rows) before.native.machine.heap).1 := by
  obtain ⟨keeps,semantic,costs,fields,known⟩ := SourceCurrentRequiredHeapEffects.node_constructor
    (FieldAvailable before.operations) rows _ good.semantic good.costs good.fields resident
  exact ⟨same_operations good _ keeps semantic costs fields,known⟩

omit [DecidableEq Symbol] in
private theorem edge_constructor {before : Checked width} (good : Good before) (symbol : Symbol) (guard : Guard)
    (values : List Node) (field : FieldAvailable before.operations guard)
    (available : Values before.native.machine.heap values) :
    Effect before (advancePhysical before ⟨(run (makeEdge symbol guard values) before.native.machine.heap).2,before.operations⟩) ∧
      EdgeResident (run (makeEdge symbol guard values) before.native.machine.heap).2
        (run (makeEdge symbol guard values) before.native.machine.heap).1 := by
  have checked := SourceEqualityRequiredCache.edge symbol guard values _ good.heap available
  have semantic := SourceEqualityRequiredSemanticCache.edge symbol guard values _ good.semantic available
  have fields := SourceEqualityAnnotationHeap.run (FieldAvailable before.operations) _
    (SourceEqualityAnnotationHeap.makeEdge _ symbol guard values field) _ good.fields
  exact ⟨same_operations good _ checked.1 semantic good.costs fields,checked.2.1⟩

omit [DecidableEq Symbol] in
private theorem shared_head {h value before result after}
    (actual : SourceCurrentAllocatedSharedEditWorker.head h value before = .done result after)
    (good : SharedGood (width := width) before) (available : Available before.checked.native.machine.heap value) :
    Effect before.checked after.checked ∧ SharedGood after ∧ Available after.checked.native.machine.heap result := by
  cases returned : SourceEqualityRequiredWorker.head h value before.checked.native.machine.heap with
  | pending | unresolved | exhausted => simp only [SourceCurrentAllocatedSharedEditWorker.head,returned] at actual; cases actual
  | done output heap =>
    simp only [SourceCurrentAllocatedSharedEditWorker.head,returned] at actual
    cases actual
    have graph := SourceEqualityRequiredWorkerSound.head_graph h value _ _ heap returned
    obtain ⟨keeps,semantic,costs,fields,known⟩ := SourceCurrentRequiredHeapEffects.head
      (FieldAvailable before.checked.operations) graph good.checked.semantic good.checked.costs good.checked.fields available
    have effect := same_operations good.checked heap keeps semantic costs fields
    exact ⟨effect,shared_advance good effect,known⟩

private def ChildContract
    (recur : SourceEqualityEdits.Edits EqualityNormalize.Path → Node → Shared width → SourceCurrentAllocatedSharedEditWorker.Outcome width Node)
    (originals : List Node) : Prop :=
  ∀ edits value before output after, recur edits value before = .done output after →
    SharedGood before → Values before.checked.native.machine.heap originals → Available before.checked.native.machine.heap value →
    Effect before.checked after.checked ∧ SharedGood after ∧ Available after.checked.native.machine.heap output

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem edit_children
    (recur : SourceEqualityEdits.Edits EqualityNormalize.Path → Node → Shared width → SourceCurrentAllocatedSharedEditWorker.Outcome width Node)
    {originals : List Node} (child : ChildContract recur originals) {entries index values before results after}
    (actual : SourceCurrentAllocatedSharedEditWorker.children recur entries index values before = .done results after)
    (good : SharedGood before) (originalsAvailable : Values before.checked.native.machine.heap originals)
    (available : Values before.checked.native.machine.heap values) :
    Effect before.checked after.checked ∧ SharedGood after ∧ Values after.checked.native.machine.heap results := by
  induction values generalizing index before results after with
  | nil => cases actual; exact ⟨.refl _ good.checked,good,by simp [Values]⟩
  | cons value values ih =>
    cases found : SourceEqualityNeededMap.lookup (index : Int) entries with
    | none =>
      simp only [SourceCurrentAllocatedSharedEditWorker.children,found] at actual
      obtain ⟨tail,final,rest,returned⟩ := shared_bind_done _ _ actual
      cases returned
      obtain ⟨effect,current,known⟩ := ih rest good originalsAvailable
        (fun value member => available value (List.mem_cons_of_mem _ member))
      refine ⟨effect,current,?_⟩
      intro output member
      rcases List.mem_cons.mp member with rfl | member
      · exact effect.keeps.available _ (available _ List.mem_cons_self)
      · exact known output member
    | some edits =>
      simp only [SourceCurrentAllocatedSharedEditWorker.children,found] at actual
      obtain ⟨result,middle,first,later⟩ := shared_bind_done _ _ actual
      obtain ⟨tail,final,rest,returned⟩ := shared_bind_done _ _ later
      cases returned
      obtain ⟨firstEffect,current,known⟩ := child edits value before result middle first good originalsAvailable (available _ List.mem_cons_self)
      obtain ⟨lastEffect,finalGood,tailKnown⟩ := ih rest current
        (fun value member => firstEffect.keeps.available value (originalsAvailable value member))
        (fun value member => firstEffect.keeps.available value (available value (List.mem_cons_of_mem _ member)))
      refine ⟨firstEffect.trans lastEffect,finalGood,?_⟩
      intro output member
      rcases List.mem_cons.mp member with rfl | member
      · exact lastEffect.keeps.available _ known
      · exact tailKnown output member

omit [DecidableEq Symbol] in
private theorem edit_rows
    (recur : SourceEqualityEdits.Edits EqualityNormalize.Path → Node → Shared width → SourceCurrentAllocatedSharedEditWorker.Outcome width Node)
    {originals : List Node} (child : ChildContract recur originals) {entries rows before results after}
    (actual : SourceCurrentAllocatedSharedEditWorker.rows recur entries rows before = .done results after)
    (good : SharedGood before) (originalsAvailable : Values before.checked.native.machine.heap originals)
    (resident : Edges before.checked.native.machine.heap rows) :
    Effect before.checked after.checked ∧ SharedGood after ∧ Edges after.checked.native.machine.heap results := by
  induction rows generalizing before results after with
  | nil => cases actual; exact ⟨.refl _ good.checked,good,by simp [Edges]⟩
  | cons edge rows ih =>
    obtain ⟨values,middle,children,later⟩ := shared_bind_done _ _ actual
    obtain ⟨firstEffect,current,known⟩ := edit_children recur child children good originalsAvailable
      (good.checked.heap.semantic.1.normal.facts.cached.edges _ _ (resident _ List.mem_cons_self))
    obtain ⟨rebuilt,afterEdge,built,later⟩ := shared_bind_done _ _ later
    have field := (good.checked.fields _ _ (resident _ List.mem_cons_self)).grows firstEffect.operations
    have checked := edge_constructor current.checked edge.entry.key.symbol edge.entry.key.constraint values field known
    simp only [SourceCurrentAllocatedSharedEditWorker.work] at built
    cases built
    obtain ⟨tail,final,rest,returned⟩ := shared_bind_done _ _ later
    cases returned
    have edgeGood := shared_advance current checked.1
    have prefixEffect := firstEffect.trans checked.1
    obtain ⟨lastEffect,finalGood,tailKnown⟩ := ih rest edgeGood
      (fun value member => prefixEffect.keeps.available value (originalsAvailable value member))
      (fun edge member => edge_grows _ _ prefixEffect.keeps.growth edge (resident edge (List.mem_cons_of_mem _ member)))
    refine ⟨prefixEffect.trans lastEffect,finalGood,?_⟩
    intro output member
    rcases List.mem_cons.mp member with rfl | member
    · exact edge_grows _ _ lastEffect.keeps.growth _ checked.2
    · exact tailKnown output member

/-- Literal edit recursion derives all reached fields and available values without a range certificate. -/
theorem edit {record originals e p h m s n edits value before result after}
    (actual : SourceCurrentAllocatedSharedEditWorker.edit record originals e p h m s n edits value before = .done result after)
    (good : SharedGood (width := width) before) (originalsAvailable : Values before.checked.native.machine.heap originals)
    (available : Available before.checked.native.machine.heap value) :
    Effect before.checked after.checked ∧ SharedGood after ∧ Available after.checked.native.machine.heap result := by
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
        exact leaf observed good originalsAvailable available
    | editBelow entries =>
      cases value with
      | empty => cases actual; exact ⟨.refl _ good.checked,good,empty_available _⟩
      | reference => cases actual
      | node entry rows depth free =>
        obtain ⟨rebuilt,middle,first,last⟩ := shared_bind_done _ _ actual
        have resident := InternedEdgeResidency.resident_edges _ good.checked.heap.semantic.1.normal.facts.linked _ available.resident
        obtain ⟨effect,current,known⟩ := edit_rows _ (fun _ _ _ _ _ => ih) first good originalsAvailable resident
        have checked := node_constructor current.checked rebuilt known
        simp only [SourceCurrentAllocatedSharedEditWorker.work] at last
        cases last
        exact ⟨effect.trans checked.1,shared_advance current checked.1,checked.2⟩
      | mu | union =>
        obtain ⟨exposed,middle,first,last⟩ := shared_bind_done _ _ actual
        obtain ⟨effect,current,known⟩ := shared_head first good available
        obtain ⟨lastEffect,finalGood,returned⟩ := ih last current
          (fun value member => effect.keeps.available value (originalsAvailable value member)) known
        exact ⟨effect.trans lastEffect,finalGood,returned⟩

/-- An actual class edit list retains every available input position and physical cache. -/
theorem edit_list {record originals e p h m s n edits values before results after}
    (actual : SourceCurrentAllocatedSharedEditWorker.editList
      (SourceCurrentAllocatedSharedEditWorker.edit record originals e p h m s n) edits values before = .done results after)
    (good : SharedGood (width := width) before) (originalsAvailable : Values before.checked.native.machine.heap originals)
    (available : Values before.checked.native.machine.heap values) :
    Effect before.checked after.checked ∧ SharedGood after ∧ Values after.checked.native.machine.heap results := by
  cases edits with
  | editAt => cases actual; exact ⟨.refl _ good.checked,good,available⟩
  | editBelow entries => exact edit_children _ (fun _ _ _ _ _ => edit) actual good originalsAvailable available

/-- A completed class starts with empty slots and derives all final physical fields. -/
theorem run_class {e p h m s n record values before memo results after saved}
    (actual : SourceCurrentAllocatedClassWorker.runClass e p h m s n record values before memo = .done results after saved)
    (good : Good (width := width) before) (stored : Stored before.native.machine.heap memo)
    (available : Values before.native.machine.heap values) :
    Effect before after ∧ Stored after.native.machine.heap saved ∧ Values after.native.machine.heap results := by
  cases returned : SourceCurrentAllocatedSharedEditWorker.editList
      (SourceCurrentAllocatedSharedEditWorker.edit record values e p h m s n)
      (SourceCurrentAllocatedClassEditPlan.compiled record) values (SourceCurrentAllocatedSharedTargetState.initial before memo) with
  | failed => simp only [SourceCurrentAllocatedClassWorker.runClass,returned] at actual; cases actual
  | done output shared =>
    simp only [SourceCurrentAllocatedClassWorker.runClass,returned] at actual
    cases actual
    obtain ⟨effect,final,known⟩ := edit_list returned (SharedGood.initial good stored) available available
    exact ⟨effect,final.stored,known⟩

private theorem class_bind_done
    (first : SourceCurrentAllocatedClassWorker.Outcome width)
    (next : List Node → Checked width → Memo → SourceCurrentAllocatedClassWorker.Outcome width)
    {output : List Node} {after : Checked width} {saved : Memo} (actual : first.bind next = .done output after saved) :
    ∃ value middle current, first = .done value middle current ∧ next value middle current = .done output after saved := by
  cases first with
  | done value middle current => exact ⟨value,middle,current,rfl,actual⟩
  | failed => cases actual

/-- A complete right fold derives invariants at each actual tail and head return. -/
theorem class_fold {e p h m s n records values before memo results after saved}
    (actual : SourceCurrentAllocatedClassWorker.fold e p h m s n records values before memo = .done results after saved)
    (good : Good (width := width) before) (stored : Stored before.native.machine.heap memo)
    (available : Values before.native.machine.heap values) :
    Effect before after ∧ Stored after.native.machine.heap saved ∧ Values after.native.machine.heap results := by
  induction records generalizing values before memo results after saved with
  | nil => cases actual; exact ⟨.refl _ good,stored,available⟩
  | cons record records ih =>
    obtain ⟨middle,checked,current,first,last⟩ := class_bind_done _ _ actual
    obtain ⟨effect,retained,known⟩ := ih first good stored available
    obtain ⟨remaining,stored,known⟩ := run_class last effect.good retained known
    exact ⟨effect.trans remaining,stored,known⟩

/-- A complete class pass retains full operation validity and actual propagated value residency. -/
theorem class_pass {e p h m s n records values before memo results after saved}
    (actual : SourceCurrentAllocatedClassWorker.pass e p h m s n records values before memo = .done results after saved)
    (good : Good (width := width) before) (stored : Stored before.native.machine.heap memo)
    (available : Values before.native.machine.heap values) :
    Effect before after ∧ Stored after.native.machine.heap saved ∧ Values after.native.machine.heap results := by
  obtain ⟨middle,checked,current,first,last⟩ := class_bind_done _ _ actual
  cases last
  obtain ⟨effect,stored,known⟩ := class_fold first good stored available
  refine ⟨effect,stored,?_⟩
  unfold EqualityLeafProjectionRuntimeEmpty.propagate
  split
  · intro value member
    obtain ⟨original,_,same⟩ := List.mem_map.mp member
    cases same
    exact empty_available _
  · exact known

end MicroCFTA.SourceCurrentLowerOperationInvariants
