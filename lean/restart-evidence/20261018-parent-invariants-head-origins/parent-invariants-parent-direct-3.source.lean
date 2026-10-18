import MicroCFTA.SourceCurrentLowerOperationInvariants

/-!
# Physical invariants from literal completed Parent execution

Initial physical operands, stored merge entries, and allocated fields suffice.
Every reached prefix follows its actual successful worker equation. The proof
uses no reached ranges, semantic native result law, or supplied call graph.
It does not prove that a general Parent or outer call completes.
-/
namespace MicroCFTA.SourceCurrentParentOperationInvariants
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentNativeOperationHeap (Good)
open SourceCurrentLowerOperationInvariants (Effect)
open SourceCurrentMemoMergeEffects (Stored)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "FieldAvailable" => SourceCurrentConjunctionEquality.FieldAvailable
local notation "Effects" => SourceCurrentConjunctionRowsAllocation.Effects
variable {width : Nat}

private theorem advanced {before : Checked width} (good : Good before) {after : Physical}
    (effects : Effects (physical before) after) : Effect before (advancePhysical before after) :=
  ⟨good.advance after effects,effects.keeps,effects.grows⟩

private theorem physical_only {before : Checked width} (good : Good before)
    (heap : State Symbol Guard) (keeps : SourceEqualityRequiredCache.Keeps before.native.machine.heap heap)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady heap)
    (costs : InternedFreshOrdinaryCostHeap.Heap heap)
    (fields : SourceCurrentConjunctionEquality.Fields before.operations heap) :
    Effect before (advancePhysical before ⟨heap,before.operations⟩) :=
  advanced good ⟨keeps,⟨semantic,costs,good.operations,fields⟩,SourceEqualityConstraintMemoAllocation.grows_refl _⟩

private theorem query [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {n left right before result after}
    (actual : SourceEqualityNativeDemand.execute n
      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) before = .done result after)
    (good : Good (width := width) before) (first : Available before.native.machine.heap left)
    (second : Available before.native.machine.heap right) : Effect before after ∧ Available after.native.machine.heap result := by
  have ready : SourceRecursiveIntersectionThunks.NodeReady before.native.machine
      ⟨IntersectionEmptyDomain.emptyDomain,left,right⟩ :=
    ⟨SourceRecursiveIntersectionKernel.empty_domain before.native.machine,first,second⟩
  obtain ⟨final,_,keeps,growth,known⟩ := SourceCurrentNativeOperationHeap.node n _ before after result good ready actual
  exact ⟨⟨final,keeps,growth⟩,known⟩

private theorem seeded_operand [DecidableEq (EdgeKey Symbol Guard)] {p h path values before result after}
    (actual : SourceCurrentAllocatedSeededWorker.operand p h path values before = .done result after)
    (good : Good (width := width) before) (available : Values before.native.machine.heap values) :
    Effect before after ∧ Available after.native.machine.heap result := by
  cases observed : SourceEqualityProjectionWorker.forest p h path values before.native.machine.heap with
  | pending | unresolved | exhausted => simp only [SourceCurrentAllocatedSeededWorker.operand,observed] at actual; cases actual
  | done value heap =>
    simp only [SourceCurrentAllocatedSeededWorker.operand,observed] at actual
    cases actual
    have graph := SourceEqualityProjectionWorkerSound.forest_graph _ _ _ _ _ _ _ observed
    have checked := SourceEqualityProjectionCosts.forest_effects graph good.semantic good.costs available
    have fields := SourceCurrentOpenProjectionFields.forest (FieldAvailable before.operations)
      graph good.semantic good.costs available good.fields
    exact ⟨physical_only good _ checked.1 checked.2.1 checked.2.2.1 fields,checked.2.2.2⟩

private theorem seeded_bind_done
    (first : SourceCurrentAllocatedSeededWorker.Outcome width)
    (next : Node → Checked width → SourceCurrentAllocatedSeededWorker.Outcome width)
    {output : Node} {after : Checked width} (actual : first.bind next = .done output after) :
    ∃ value middle, first = .done value middle ∧ next value middle = .done output after := by
  cases first with
  | done value middle => exact ⟨value,middle,rfl,actual⟩
  | failed => cases actual

private theorem seeded_leaf [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {n left right before result after}
    (actual : SourceCurrentAllocatedSeededWorker.leaf n left right before = .done result after)
    (good : Good (width := width) before) (first : Available before.native.machine.heap left)
    (second : Available before.native.machine.heap right) : Effect before after ∧ Available after.native.machine.heap result := by
  cases observed : SourceEqualityNativeDemand.execute n
      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) before with
  | yielded | failed | constraintError | blocked => simp only [SourceCurrentAllocatedSeededWorker.leaf,observed] at actual; cases actual
  | done value checked =>
    simp only [SourceCurrentAllocatedSeededWorker.leaf,observed] at actual
    cases actual
    exact query observed good first second

private theorem seeded_fold [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {p h n values seed paths before result after}
    (actual : SourceCurrentAllocatedSeededWorker.fold p h n values seed paths before = .done result after)
    (good : Good (width := width) before) (available : Values before.native.machine.heap values) :
    Effect before after ∧ Available after.native.machine.heap result := by
  induction paths generalizing before result after with
  | nil => exact seeded_operand actual good available
  | cons path paths ih =>
    obtain ⟨head,middle,first,later⟩ := seeded_bind_done _ _ actual
    obtain ⟨headEffect,known⟩ := seeded_operand first good available
    obtain ⟨tail,final,rest,last⟩ := seeded_bind_done _ _ later
    obtain ⟨tailEffect,tailKnown⟩ := ih rest headEffect.good
      (fun value member => headEffect.keeps.available value (available value member))
    obtain ⟨effect,known⟩ := seeded_leaf last tailEffect.good (tailEffect.keeps.available _ known) tailKnown
    exact ⟨(headEffect.trans tailEffect).trans effect,known⟩

/-- Completed seeded queries retain physical validity without selected-domain or reached-range inputs. -/
theorem seeded [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {p h n values paths before result after}
    (actual : SourceCurrentAllocatedSeededWorker.seeded p h n values paths before = .done result after)
    (good : Good (width := width) before) (available : Values before.native.machine.heap values) :
    Effect before after ∧ Available after.native.machine.heap result := by
  cases paths with
  | nil => cases actual; exact ⟨.refl _ good,empty_available _⟩
  | cons seed paths => exact seeded_fold actual good available

private theorem gate [DecidableEq (EdgeKey Symbol Guard)] {below fuel values paths before fourth answer after saved}
    (actual : SourceCurrentAllocatedScanWorker.gate below fuel values paths before fourth = .done answer after saved)
    (good : Good (width := width) before) (available : Values before.native.machine.heap values) : Effect before after := by
  cases below with
  | true =>
    cases observed : SourceCurrentAllocatedGateWorker.primary fuel values paths before with
    | failed => simp only [SourceCurrentAllocatedScanWorker.gate,ite_true,observed] at actual; cases actual
    | done value checked =>
      simp only [SourceCurrentAllocatedScanWorker.gate,ite_true,observed] at actual
      cases actual
      have graph := SourceCurrentAllocatedGateWorker.primary_graph observed
      have effects := SourceCurrentAllocatedGateFields.primary_class _ _ graph good.physical available
      have effect := advanced good effects.1
      have same := (SourceCurrentAllocatedGateWorker.primary_done observed).2
      exact same.symm ▸ effect
  | false =>
    cases observed : SourceCurrentAllocatedGateWorker.secondary fuel values paths before with
    | failed => simp only [SourceCurrentAllocatedScanWorker.gate,Bool.false_eq_true,ite_false,observed] at actual; cases actual
    | done value checked =>
      simp only [SourceCurrentAllocatedScanWorker.gate,Bool.false_eq_true,ite_false,observed] at actual
      cases actual
      have graph := SourceCurrentAllocatedGateWorker.secondary_graph observed
      have effects := SourceCurrentAllocatedGateFields.secondary_class _ graph good.physical available
      have effect := advanced good effects.1
      have same := (SourceCurrentAllocatedGateWorker.secondary_done observed).2
      exact same.symm ▸ effect

private theorem scan_query [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {p h n values paths before fourth result after saved}
    (actual : SourceCurrentAllocatedScanWorker.query p h n values paths before fourth = .done result after saved)
    (good : Good (width := width) before) (available : Values before.native.machine.heap values) :
    Effect before after ∧ Available after.native.machine.heap result := by
  cases observed : SourceCurrentAllocatedSeededWorker.seeded p h n values (paths.map (List.map Int.ofNat)) before with
  | failed => simp only [SourceCurrentAllocatedScanWorker.query,observed] at actual; cases actual
  | done value checked =>
    simp only [SourceCurrentAllocatedScanWorker.query,observed] at actual
    cases actual
    exact seeded observed good available

private theorem scan_decision [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
    {p h budget paths value before fourth answer after saved}
    (actual : SourceCurrentAllocatedScanWorker.decision p h budget paths value before fourth = .done answer after saved)
    (good : Good (width := width) before) (available : Available before.native.machine.heap value) : Effect before after := by
  cases observed : SourceCurrentAllocatedConjunctionWorker.call p h budget value before fourth with
  | failed => simp only [SourceCurrentAllocatedScanWorker.decision,observed] at actual; cases actual
  | done result checked current =>
    simp only [SourceCurrentAllocatedScanWorker.decision,observed] at actual
    cases actual
    obtain ⟨heap,done,rfl⟩ := SourceCurrentAllocatedConjunctionWorker.call_done observed
    have graph := SourceCurrentConjunctionWorkerCompletion.call_sound p h budget fourth value (physical before) _ heap _ done
    obtain ⟨answer,heap,saved,produced,effects⟩ := SourceCurrentConjunctionMemo.complete budget fourth value (physical before) good.physical available
    obtain ⟨_,rfl,_⟩ := SourceCurrentConjunctionCallUnique.call graph produced
    exact advanced good effects

private theorem scan_bind_done {A B : Type}
    (first : SourceCurrentAllocatedScanWorker.Outcome A width)
    (next : A → Checked width → Fourth → SourceCurrentAllocatedScanWorker.Outcome B width)
    {output : B} {after : Checked width} {saved : Fourth} (actual : first.bind next = .done output after saved) :
    ∃ value middle current, first = .done value middle current ∧ next value middle current = .done output after saved := by
  cases first with
  | done value middle current => exact ⟨value,middle,current,rfl,actual⟩
  | failed => cases actual

/-- Actual class scanning derives its reached physical invariants from the original available forest. -/
theorem scan [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
    {g s p h n budget values classes before fourth result after saved}
    (actual : SourceCurrentAllocatedScanWorker.scan g s p h n budget values classes before fourth = .done result after saved)
    (good : Good (width := width) before) (available : Values before.native.machine.heap values) : Effect before after := by
  induction classes generalizing before fourth result after saved with
  | nil => cases actual; exact .refl _ good
  | cons paths classes ih =>
    obtain ⟨primary,middle,current,first,later⟩ := scan_bind_done _ _ actual
    have firstEffect := gate first good available
    have middleAvailable : Values middle.native.machine.heap values := fun value member => firstEffect.keeps.available value (available value member)
    cases primary with
    | false =>
      simp only [Bool.false_eq_true,ite_false] at later
      cases observed : SourceCurrentAllocatedScanWorker.scan g s p h n budget values classes middle current with
      | failed => simp only [observed,SourceCurrentAllocatedScanWorker.Outcome.select] at later; cases later
      | done output checked completed =>
        cases output with
        | mk stopped selected =>
          simp only [observed,SourceCurrentAllocatedScanWorker.Outcome.select] at later
          cases later
          exact firstEffect.trans (ih observed firstEffect.good middleAvailable)
    | true =>
      simp only [ite_true] at later
      obtain ⟨secondary,last,completed,second,later⟩ := scan_bind_done _ _ later
      have secondEffect := gate second firstEffect.good middleAvailable
      have prefixEffect := firstEffect.trans secondEffect
      have lastAvailable : Values last.native.machine.heap values := fun value member => prefixEffect.keeps.available value (available value member)
      cases secondary with
      | true =>
        simp only [ite_true] at later
        exact prefixEffect.trans (ih later secondEffect.good lastAvailable)
      | false =>
        simp only [Bool.false_eq_true,ite_false] at later
        obtain ⟨value,queried,next,queryDone,later⟩ := scan_bind_done _ _ later
        obtain ⟨queryEffect,known⟩ := scan_query queryDone secondEffect.good lastAvailable
        obtain ⟨answer,decided,final,decisionDone,later⟩ := scan_bind_done _ _ later
        have decisionEffect := scan_decision decisionDone queryEffect.good known
        have prefixEffect := (prefixEffect.trans queryEffect).trans decisionEffect
        cases answer with
        | true => cases later; exact prefixEffect
        | false =>
          simp only [Bool.false_eq_true,ite_false] at later
          exact prefixEffect.trans (ih later decisionEffect.good
            (fun value member => prefixEffect.keeps.available value (available value member)))

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
    exact ⟨scan paths good available,rfl⟩

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
    (available : Values before.native.machine.heap values) :
    Effect before after ∧ Stored after.native.machine.heap current ∧ Values after.native.machine.heap results := by
  cases observed : SourceCurrentAllocatedClassWorker.pass e p h m s n records values before memo with
  | failed => simp only [SourceCurrentAllocatedLocalWorker.pass,observed] at actual; cases actual
  | done output checked completed =>
    simp only [SourceCurrentAllocatedLocalWorker.pass,observed] at actual
    cases actual
    exact SourceCurrentLowerOperationInvariants.class_pass observed good stored available

/-- The completed Scan, Required, and class-pass continuation derives every intermediate physical state. -/
theorem classes [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
    {g s r e p h m c n budget records values before fourth memo results after saved current}
    (actual : SourceCurrentAllocatedLocalWorker.classes g s r e p h m c n budget records values before fourth memo = .done results after saved current)
    (good : Good (width := width) before) (stored : Stored before.native.machine.heap memo)
    (available : Values before.native.machine.heap values) :
    Effect before after ∧ Stored after.native.machine.heap current ∧ Values after.native.machine.heap results := by
  obtain ⟨result,middle,completed,current,first,later⟩ := local_bind_done _ _ actual
  obtain ⟨effect,rfl⟩ := local_scan first good available
  cases stopped : result.1 with
  | some paths =>
    simp only [stopped] at later
    cases later
    refine ⟨effect,stored.grows effect.keeps,?_⟩
    intro value member
    obtain ⟨original,_,same⟩ := List.mem_map.mp member
    cases same
    exact empty_available _
  | none =>
    simp only [stopped] at later
    obtain ⟨required,checked,following,warm,requiredDone,passDone⟩ := local_bind_done _ _ later
    obtain ⟨firstEffect,known,_,rfl⟩ := local_required requiredDone effect.good
      (fun value member => effect.keeps.available value (available value member))
    obtain ⟨lastEffect,retained,returned⟩ := local_pass passDone firstEffect.good
      (stored.grows (effect.keeps.trans firstEffect.keeps)) known
    exact ⟨(effect.trans firstEffect).trans lastEffect,retained,returned⟩

private theorem precheck (loaded : Allocated) (inherited : EqValue) (before : Checked width)
    (good : Good before) (stored : EqReady before.operations.constraints loaded.stored)
    (ready : EqReady before.operations.constraints inherited) :
    let current := SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard inherited before.operations
    Effect before (advancePhysical before ⟨before.native.machine.heap,current.2⟩) := by
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
  have effects : Effects (physical before)
      ⟨before.native.machine.heap,(SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard inherited before.operations).2⟩ := by
    rw [same]
    exact ⟨SourceEqualityRequiredCache.pure_keeps _ good.heap,
      ⟨good.semantic,good.costs,checked.2.1,good.fields.grows total⟩,total⟩
  exact advanced good effects

/-- A literal local reduction derives its full returned physical invariants from initial ready operands. -/
theorem reduce [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
    {g s r e p h m c n budget loaded inherited values before fourth memo results after saved current}
    (actual : SourceCurrentAllocatedLocalWorker.reduce g s r e p h m c n budget loaded inherited values before fourth memo = .done results after saved current)
    (good : Good (width := width) before) (stored : Stored before.native.machine.heap memo)
    (loadedReady : EqReady before.operations.constraints loaded.stored)
    (inheritedReady : EqReady before.operations.constraints inherited) (available : Values before.native.machine.heap values) :
    Effect before after ∧ Stored after.native.machine.heap current ∧ Values after.native.machine.heap results := by
  have prefixEffect := precheck loaded inherited before good loadedReady inheritedReady
  cases observed : (SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard inherited before.operations).1 with
  | error message => simp only [SourceCurrentAllocatedLocalWorker.reduce,observed] at actual; cases actual
  | ok branch =>
    cases branch with
    | unchanged =>
      simp only [SourceCurrentAllocatedLocalWorker.reduce,observed] at actual
      cases actual
      exact ⟨prefixEffect,stored.grows prefixEffect.keeps,
        fun value member => prefixEffect.keeps.available value (available value member)⟩
    | emptyChildren =>
      simp only [SourceCurrentAllocatedLocalWorker.reduce,observed] at actual
      cases actual
      refine ⟨prefixEffect,stored.grows prefixEffect.keeps,?_⟩
      intro value member
      obtain ⟨original,_,same⟩ := List.mem_map.mp member
      cases same
      exact empty_available _
    | classes records =>
      simp only [SourceCurrentAllocatedLocalWorker.reduce,observed] at actual
      obtain ⟨effect,retained,known⟩ := classes actual prefixEffect.good (stored.grows prefixEffect.keeps)
        (fun value member => prefixEffect.keeps.available value (available value member))
      exact ⟨prefixEffect.trans effect,retained,known⟩

private theorem raw_edge (before : Checked width) (good : Good before)
    (operations : SourceEqualityConstraintMemoAllocation.State) (valid : SourceEqualityConstraintMemoAllocation.Valid operations)
    (growth : SourceEqualityConstraintMemoAllocation.Grows before.operations operations)
    (symbol : Symbol) (guard : Guard) (values : List Node) (field : FieldAvailable operations guard)
    (available : Values before.native.machine.heap values) :
    let built := run (makeEdge symbol guard values) before.native.machine.heap
    Effect before (advancePhysical before ⟨built.2,operations⟩) ∧ EdgeResident built.2 built.1 := by
  classical
  have built := SourceEqualityRequiredCache.edge symbol guard values _ good.heap available
  have semantic := SourceEqualityRequiredSemanticCache.edge symbol guard values _ good.semantic available
  have fields := SourceEqualityAnnotationHeap.run (FieldAvailable operations) _
    (SourceEqualityAnnotationHeap.makeEdge _ symbol guard values field) _ (good.fields.grows growth)
  exact ⟨advanced good ⟨built.1,⟨semantic,good.costs,valid,fields⟩,growth⟩,built.2.1⟩

/-- Raw rejection derives its own Top field and sentinel without child, field, or inherited inputs. -/
theorem reject [DecidableEq (EdgeKey Symbol Guard)] (symbol : Symbol) (before : Checked width) (good : Good before) :
    Effect before (SourceCurrentAllocatedMkEdge.reject symbol before).2 ∧
      EdgeResident (SourceCurrentAllocatedMkEdge.reject symbol before).2.native.machine.heap
        (SourceCurrentAllocatedMkEdge.reject symbol before).1 := by
  obtain ⟨valid,growth,field⟩ := SourceCurrentConjunctionFieldAllocation.empty_field before.operations good.operations
  exact raw_edge before good _ valid growth symbol SourceEqualityConstraintConstructors.top [.empty] field
    (by intro value member; cases List.mem_singleton.mp member; exact empty_available _)

/-- The actual checked constructor derives all operation and resident-row invariants from initial ready inputs. -/
theorem build [DecidableEq (EdgeKey Symbol Guard)] {symbol loaded children before result after}
    (actual : SourceCurrentAllocatedMkEdge.build symbol loaded children before = (.ok result,after))
    (good : Good (width := width) before) (loadedReady : EqReady before.operations.constraints loaded.stored)
    (field : FieldAvailable before.operations (SourceEqualityConjoinAllocation.readback loaded))
    (available : Values before.native.machine.heap children) : Effect before after ∧ EdgeResident after.native.machine.heap result := by
  have checked := SourceEqualityMkEdgeAllocation.check_correct loaded.stored loaded.guard children.length
    before.operations good.operations loadedReady
  have built := SourceEqualityMkEdgeAllocation.build_receipt symbol loaded.stored loaded.guard children before.operations before.native.machine.heap
    good.operations loadedReady
  cases keep : SourceEqualityMkEdgeAllocation.accepted (SourceEqualityConjoinAllocation.readback loaded) children.length with
  | true =>
    have selected : SourceEqualityMkEdgeAllocation.accepted
        (SourceEqualityAccessorAllocation.constraint loaded.stored loaded.guard) children.length = true := keep
    have effects := raw_edge before good _ checked.2.1 checked.2.2 symbol
      (SourceEqualityConjoinAllocation.readback loaded) children (field.grows checked.2.2) available
    have equation : SourceCurrentAllocatedMkEdge.build symbol loaded children before =
        (.ok (run (makeEdge symbol (SourceEqualityConjoinAllocation.readback loaded) children) before.native.machine.heap).1,
          advancePhysical before ⟨(run (makeEdge symbol (SourceEqualityConjoinAllocation.readback loaded) children) before.native.machine.heap).2,
            (SourceEqualityMkEdgeAllocation.check loaded.stored loaded.guard children.length before.operations).2⟩) := by
      simp only [SourceCurrentAllocatedMkEdge.build,built.1,SourceEqualityMkEdgeAllocation.work,
        SourceEqualityMkEdgeAllocation.outputState,selected,ite_true]
      rfl
    obtain ⟨same,state⟩ := Prod.mk.inj (equation.symm.trans actual)
    cases Except.ok.inj same
    cases state
    exact effects
  | false =>
    have selected : SourceEqualityMkEdgeAllocation.accepted
        (SourceEqualityAccessorAllocation.constraint loaded.stored loaded.guard) children.length = false := keep
    obtain ⟨valid,growth,field⟩ := SourceCurrentConjunctionFieldAllocation.empty_field _ checked.2.1
    have effects := raw_edge before good _ valid (SourceCurrentConjunctionEquality.grows_trans checked.2.2 growth)
      symbol SourceEqualityConstraintConstructors.top [.empty] field
      (by intro value member; cases List.mem_singleton.mp member; exact empty_available _)
    have equation : SourceCurrentAllocatedMkEdge.build symbol loaded children before =
        (.ok (run (makeEdge symbol SourceEqualityConstraintConstructors.top [.empty]) before.native.machine.heap).1,
          advancePhysical before ⟨(run (makeEdge symbol SourceEqualityConstraintConstructors.top [.empty]) before.native.machine.heap).2,
            SourceEqualityMkEdgeAllocation.emptyField (SourceEqualityMkEdgeAllocation.check loaded.stored loaded.guard children.length before.operations).2⟩) := by
      simp only [SourceCurrentAllocatedMkEdge.build,built.1,SourceEqualityMkEdgeAllocation.work,
        SourceEqualityMkEdgeAllocation.outputState,selected,Bool.false_eq_true,ite_false]
    obtain ⟨same,state⟩ := Prod.mk.inj (equation.symm.trans actual)
    cases Except.ok.inj same
    cases state
    exact effects

private theorem parent_bind_done {A B : Type}
    (first : SourceCurrentAllocatedParentWorker.Outcome A width)
    (next : A → Checked width → Fourth → Memo → SourceCurrentAllocatedParentWorker.Outcome B width)
    {output : B} {after : Checked width} {fourth : Fourth} {saved : Memo}
    (actual : first.bind next = .done output after fourth saved) :
    ∃ value middle current memo, first = .done value middle current memo ∧ next value middle current memo = .done output after fourth saved := by
  cases first with
  | done value middle current memo => exact ⟨value,middle,current,memo,rfl,actual⟩
  | failed => cases actual

/-- Every completed Parent derives its full physical invariant without any reached range or graph input. -/
theorem parent [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
    {g s r e p h m c n budget symbol original inherited children before fourth memo result after saved current}
    (actual : SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget symbol original inherited children before fourth memo =
      .done result after saved current)
    (good : Good (width := width) before) (stored : Stored before.native.machine.heap memo)
    (live : SourceEqualityMkEdgeAllocation.contradictory original = false →
      FieldAvailable before.operations original ∧ EqReady before.operations.constraints inherited ∧ Values before.native.machine.heap children) :
    Effect before after ∧ Stored after.native.machine.heap current ∧ EdgeResident after.native.machine.heap result := by
  cases rejected : SourceEqualityMkEdgeAllocation.contradictory original with
  | true =>
    simp only [SourceCurrentAllocatedParentWorker.edge,rejected,ite_true] at actual
    cases actual
    have effects := reject symbol before good
    exact ⟨effects.1,stored.grows effects.1.keeps,effects.2⟩
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
        obtain ⟨effect,retained,known⟩ := reduce reduced good stored properties.1 inheritedReady available
        have currentReady := properties.1.grows effect.operations.constraint_growth
        have currentField : FieldAvailable middle.operations (SourceEqualityConjoinAllocation.readback loadedValue) :=
          properties.2.symm ▸ field.grows effect.operations
        cases observed : SourceCurrentAllocatedMkEdge.build symbol loadedValue values middle with
        | mk returned checked =>
          cases returned with
          | error => simp only [SourceCurrentAllocatedParentWorker.build,observed] at last; cases last
          | ok value =>
            simp only [SourceCurrentAllocatedParentWorker.build,observed] at last
            cases last
            obtain ⟨lastEffect,resident⟩ := build observed effect.good currentReady currentField known
            exact ⟨effect.trans lastEffect,retained.grows lastEffect.keeps,resident⟩

end MicroCFTA.SourceCurrentParentOperationInvariants
