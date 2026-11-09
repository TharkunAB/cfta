import MicroCFTA.SourceCurrentParentProbeHeap
import MicroCFTA.SourceCurrentAllocatedSharedParentWorker
import MicroCFTA.SourceCurrentConjunctionSharedWorkerEffects
import MicroCFTA.SourceCurrentConjunctionSharedWorkerProbes

/-!
# Physical probes through completed shared Parent execution

The proof follows each actual shared Scan, Local and Parent return. The
unchanged gate, seeded and constructor laws apply to their literal callees.
Shared decisions retain the same private snapshot and physical endpoint.
Initial physical readiness and stored merge values supply the invariant.
No caller Context, resource reservation or future state is a premise.
These laws concern successful returns and do not prove completion.
-/
namespace MicroCFTA.SourceCurrentSharedParentProbeHeap
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentLowerProbeHeap (Good)
open SourceCurrentLowerProbeHeap (Effect)
open SourceCurrentMemoMergeEffects (Stored)
open SourceCurrentParentProbeHeap (seeded reject build)
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
    (effects : Effects (physical before) after) (probes : InternedFreshOrdinaryProbeHeap.Heap after.heap) :
    Effect before (advancePhysical before after) :=
  ⟨good.advance after effects probes,effects.keeps,effects.grows⟩

private theorem physical_only {before : Checked width} (good : Good before)
    (heap : State Symbol Guard) (keeps : SourceEqualityRequiredCache.Keeps before.native.machine.heap heap)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady heap)
    (costs : InternedFreshOrdinaryCostHeap.Heap heap)
    (fields : SourceCurrentConjunctionEquality.Fields before.operations heap)
    (probes : InternedFreshOrdinaryProbeHeap.Heap heap) :
    Effect before (advancePhysical before ⟨heap,before.operations⟩) :=
  advanced good ⟨keeps,⟨semantic,costs,good.operations,fields⟩,SourceEqualityConstraintMemoAllocation.grows_refl _⟩ probes

private theorem gate [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {below fuel values paths before fourth answer after saved}
    (actual : SourceCurrentAllocatedSharedScanWorker.gate below fuel values paths before fourth = .done answer after saved)
    (good : Good (width := width) before) (available : Values before.native.machine.heap values) : Effect before after := by
  cases below with
  | true =>
    cases observed : SourceCurrentAllocatedGateWorker.primary fuel values paths before with
    | failed => simp only [SourceCurrentAllocatedSharedScanWorker.gate,ite_true,observed] at actual; cases actual
    | done value checked =>
      simp only [SourceCurrentAllocatedSharedScanWorker.gate,ite_true,observed] at actual
      cases actual
      have graph := SourceCurrentAllocatedGateWorker.primary_graph observed
      have effects := SourceCurrentAllocatedGateFields.primary_class _ _ graph good.physical available
      have probes := (SourceCurrentAllocatedProbeGates.Primary.class_effects _ _ graph good.semantic good.costs available good.probes).2.2.2
      have effect := advanced good effects.1 probes
      have same := (SourceCurrentAllocatedGateWorker.primary_done observed).2
      exact same.symm ▸ effect
  | false =>
    cases observed : SourceCurrentAllocatedGateWorker.secondary fuel values paths before with
    | failed => simp only [SourceCurrentAllocatedSharedScanWorker.gate,Bool.false_eq_true,ite_false,observed] at actual; cases actual
    | done value checked =>
      simp only [SourceCurrentAllocatedSharedScanWorker.gate,Bool.false_eq_true,ite_false,observed] at actual
      cases actual
      have graph := SourceCurrentAllocatedGateWorker.secondary_graph observed
      have effects := SourceCurrentAllocatedGateFields.secondary_class _ graph good.physical available
      have probes := (SourceCurrentAllocatedProbeGates.Secondary.class_effects _ graph good.semantic good.costs available good.probes).2.2.2
      have effect := advanced good effects.1 probes
      have same := (SourceCurrentAllocatedGateWorker.secondary_done observed).2
      exact same.symm ▸ effect

private theorem scan_query [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
    {p h n values paths before fourth result after saved}
    (actual : SourceCurrentAllocatedSharedScanWorker.query p h n values paths before fourth = .done result after saved)
    (good : Good (width := width) before) (available : Values before.native.machine.heap values) :
    Effect before after ∧ Available after.native.machine.heap result := by
  cases observed : SourceCurrentAllocatedSeededWorker.seeded p h n values (paths.map (List.map Int.ofNat)) before with
  | failed => simp only [SourceCurrentAllocatedSharedScanWorker.query,observed] at actual; cases actual
  | done value checked =>
    simp only [SourceCurrentAllocatedSharedScanWorker.query,observed] at actual
    cases actual
    exact seeded observed good available

private theorem scan_decision [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
    {p h budget paths value before fourth answer after saved}
    (actual : SourceCurrentAllocatedSharedScanWorker.decision p h budget paths value before fourth = .done answer after saved)
    (good : Good (width := width) before) (available : Available before.native.machine.heap value) : Effect before after := by
  obtain ⟨snapshot,observed⟩ := SourceCurrentAllocatedSharedScanWorker.decision_done actual
  obtain ⟨raw,rfl⟩ := SourceCurrentAllocatedSharedConjunctionWorker.call_done observed
  have effects := SourceCurrentConjunctionSharedWorkerEffects.call_effects p h budget fourth value
    (physical before) good.physical available
  have probes := SourceCurrentConjunctionSharedWorkerProbes.call_probes p h budget fourth value
    (physical before) good.physical good.probes available
  rw [raw] at effects probes
  exact advanced good effects.1 probes

private theorem scan_bind_done {A B : Type}
    (first : SourceCurrentAllocatedSharedScanWorker.Outcome A width)
    (next : A → Checked width → Fourth → SourceCurrentAllocatedSharedScanWorker.Outcome B width)
    {output : B} {after : Checked width} {saved : Fourth} (actual : first.bind next = .done output after saved) :
    ∃ value middle current, first = .done value middle current ∧ next value middle current = .done output after saved := by
  cases first with
  | done value middle current => exact ⟨value,middle,current,rfl,actual⟩
  | failed => cases actual

/-- Actual class scanning derives its reached physical invariants from the original available forest. -/
theorem scan [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
    {g s p h n budget values classes before fourth result after saved}
    (actual : SourceCurrentAllocatedSharedScanWorker.scan g s p h n budget values classes before fourth = .done result after saved)
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
      cases observed : SourceCurrentAllocatedSharedScanWorker.scan g s p h n budget values classes middle current with
      | failed => simp only [observed,SourceCurrentAllocatedSharedScanWorker.Outcome.select] at later; cases later
      | done output checked completed =>
        cases output with
        | mk stopped selected =>
          simp only [observed,SourceCurrentAllocatedSharedScanWorker.Outcome.select] at later
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
    (first : SourceCurrentAllocatedSharedLocalWorker.Outcome A width)
    (next : A → Checked width → Fourth → Memo → SourceCurrentAllocatedSharedLocalWorker.Outcome B width)
    {output : B} {after : Checked width} {fourth : Fourth} {saved : Memo}
    (actual : first.bind next = .done output after fourth saved) :
    ∃ value middle current memo, first = .done value middle current memo ∧ next value middle current memo = .done output after fourth saved := by
  cases first with
  | done value middle current memo => exact ⟨value,middle,current,memo,rfl,actual⟩
  | failed => cases actual

private theorem local_scan [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
    {g s p h n budget records values before fourth memo result after saved current}
    (actual : SourceCurrentAllocatedSharedLocalWorker.scan g s p h n budget records values before fourth memo = .done result after saved current)
    (good : Good (width := width) before) (available : Values before.native.machine.heap values) :
    Effect before after ∧ current = memo := by
  cases observed : SourceCurrentAllocatedSharedRecordScanWorker.scan g s p h n budget values records before fourth with
  | failed => simp only [SourceCurrentAllocatedSharedLocalWorker.scan,observed] at actual; cases actual
  | done output checked completed =>
    simp only [SourceCurrentAllocatedSharedLocalWorker.scan,observed] at actual
    cases actual
    have paths := (SourceCurrentAllocatedSharedRecordScanWorker.scan_mapPaths g s p h n budget values records before fourth).symm
    rw [observed] at paths
    exact ⟨scan paths good available,rfl⟩

private theorem local_required [DecidableEq (EdgeKey Symbol Guard)]
    {r h paths values before fourth memo results after saved current}
    (actual : SourceCurrentAllocatedSharedLocalWorker.required r h paths values before fourth memo = .done results after saved current)
    (good : Good (width := width) before) (available : Values before.native.machine.heap values) :
    Effect before after ∧ Values after.native.machine.heap results ∧ saved = fourth ∧ current = memo := by
  cases observed : SourceEqualityRequiredExecution.requireAll r h paths values before.native.machine.heap with
  | pending | unresolved | exhausted => simp only [SourceCurrentAllocatedSharedLocalWorker.required,observed] at actual; cases actual
  | done output heap =>
    simp only [SourceCurrentAllocatedSharedLocalWorker.required,observed] at actual
    cases actual
    obtain ⟨keeps,semantic,costs,fields,known⟩ := SourceCurrentRequiredHeapEffects.requireAll
      (FieldAvailable before.operations) r h paths values _ _ heap observed good.semantic good.costs good.fields available
    exact ⟨physical_only good heap keeps semantic costs fields
      (SourceCurrentAllocatedProbeRequired.requireAll r h paths values _ _ heap observed good.semantic good.costs good.probes available).2.2.2.1,known,rfl,rfl⟩

private theorem local_pass [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {e p h m s n records values before fourth memo results after saved current}
    (actual : SourceCurrentAllocatedSharedLocalWorker.pass e p h m s n records values before fourth memo = .done results after saved current)
    (good : Good (width := width) before) (stored : Stored before.native.machine.heap memo)
    (available : Values before.native.machine.heap values) :
    Effect before after ∧ Stored after.native.machine.heap current ∧ Values after.native.machine.heap results := by
  cases observed : SourceCurrentAllocatedClassWorker.pass e p h m s n records values before memo with
  | failed => simp only [SourceCurrentAllocatedSharedLocalWorker.pass,observed] at actual; cases actual
  | done output checked completed =>
    simp only [SourceCurrentAllocatedSharedLocalWorker.pass,observed] at actual
    cases actual
    exact SourceCurrentLowerProbeHeap.class_pass observed good stored available

/-- The completed Scan, Required, and class-pass continuation derives every intermediate physical state. -/
theorem classes [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
    {g s r e p h m c n budget records values before fourth memo results after saved current}
    (actual : SourceCurrentAllocatedSharedLocalWorker.classes g s r e p h m c n budget records values before fourth memo = .done results after saved current)
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
  exact advanced good effects good.probes

/-- A literal local reduction derives its full returned physical invariants from initial ready operands. -/
theorem reduce [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
    {g s r e p h m c n budget loaded inherited values before fourth memo results after saved current}
    (actual : SourceCurrentAllocatedSharedLocalWorker.reduce g s r e p h m c n budget loaded inherited values before fourth memo = .done results after saved current)
    (good : Good (width := width) before) (stored : Stored before.native.machine.heap memo)
    (loadedReady : EqReady before.operations.constraints loaded.stored)
    (inheritedReady : EqReady before.operations.constraints inherited) (available : Values before.native.machine.heap values) :
    Effect before after ∧ Stored after.native.machine.heap current ∧ Values after.native.machine.heap results := by
  have prefixEffect := precheck loaded inherited before good loadedReady inheritedReady
  cases observed : (SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard inherited before.operations).1 with
  | error message => simp only [SourceCurrentAllocatedSharedLocalWorker.reduce,observed] at actual; cases actual
  | ok branch =>
    cases branch with
    | unchanged =>
      simp only [SourceCurrentAllocatedSharedLocalWorker.reduce,observed] at actual
      cases actual
      exact ⟨prefixEffect,stored.grows prefixEffect.keeps,
        fun value member => prefixEffect.keeps.available value (available value member)⟩
    | emptyChildren =>
      simp only [SourceCurrentAllocatedSharedLocalWorker.reduce,observed] at actual
      cases actual
      refine ⟨prefixEffect,stored.grows prefixEffect.keeps,?_⟩
      intro value member
      obtain ⟨original,_,same⟩ := List.mem_map.mp member
      cases same
      exact empty_available _
    | classes records =>
      simp only [SourceCurrentAllocatedSharedLocalWorker.reduce,observed] at actual
      obtain ⟨effect,retained,known⟩ := classes actual prefixEffect.good (stored.grows prefixEffect.keeps)
        (fun value member => prefixEffect.keeps.available value (available value member))
      exact ⟨prefixEffect.trans effect,retained,known⟩

private theorem parent_bind_done {A B : Type}
    (first : SourceCurrentAllocatedSharedParentWorker.Outcome A width)
    (next : A → Checked width → Fourth → Memo → SourceCurrentAllocatedSharedParentWorker.Outcome B width)
    {output : B} {after : Checked width} {fourth : Fourth} {saved : Memo}
    (actual : first.bind next = .done output after fourth saved) :
    ∃ value middle current memo, first = .done value middle current memo ∧ next value middle current memo = .done output after fourth saved := by
  cases first with
  | done value middle current memo => exact ⟨value,middle,current,memo,rfl,actual⟩
  | failed => cases actual

/-- Every completed Parent derives its full physical invariant without any reached range or graph input. -/
theorem parent [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
    {g s r e p h m c n budget symbol original inherited children before fourth memo result after saved current}
    (actual : SourceCurrentAllocatedSharedParentWorker.edge g s r e p h m c n budget symbol original inherited children before fourth memo =
      .done result after saved current)
    (good : Good (width := width) before) (stored : Stored before.native.machine.heap memo)
    (live : SourceEqualityMkEdgeAllocation.contradictory original = false →
      FieldAvailable before.operations original ∧ EqReady before.operations.constraints inherited ∧ Values before.native.machine.heap children) :
    Effect before after ∧ Stored after.native.machine.heap current ∧ EdgeResident after.native.machine.heap result := by
  cases rejected : SourceEqualityMkEdgeAllocation.contradictory original with
  | true =>
    simp only [SourceCurrentAllocatedSharedParentWorker.edge,rejected,ite_true] at actual
    cases actual
    have effects := reject symbol before good
    exact ⟨effects.1,stored.grows effects.1.keeps,effects.2⟩
  | false =>
    obtain ⟨field,inheritedReady,available⟩ := live rejected
    simp only [SourceCurrentAllocatedSharedParentWorker.edge,rejected,Bool.false_eq_true,ite_false] at actual
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
        have reduced : SourceCurrentAllocatedSharedLocalWorker.reduce g s r e p h m c n budget
            loadedValue inherited children before fourth memo = .done values middle completed warm := by
          cases observed : SourceCurrentAllocatedSharedLocalWorker.reduce g s r e p h m c n budget
              loadedValue inherited children before fourth memo with
          | failed => simp only [SourceCurrentAllocatedSharedParentWorker.reduceChildren,observed] at first; cases first
          | done output checked next current =>
            simp only [SourceCurrentAllocatedSharedParentWorker.reduceChildren,observed] at first
            cases first
            rfl
        obtain ⟨effect,retained,known⟩ := reduce reduced good stored properties.1 inheritedReady available
        have currentReady := properties.1.grows effect.operations.constraint_growth
        have currentField : FieldAvailable middle.operations (SourceEqualityConjoinAllocation.readback loadedValue) :=
          properties.2.symm ▸ field.grows effect.operations
        cases observed : SourceCurrentAllocatedMkEdge.build symbol loadedValue values middle with
        | mk returned checked =>
          cases returned with
          | error => simp only [SourceCurrentAllocatedSharedParentWorker.build,observed] at last; cases last
          | ok value =>
            simp only [SourceCurrentAllocatedSharedParentWorker.build,observed] at last
            cases last
            obtain ⟨lastEffect,resident⟩ := build observed effect.good currentReady currentField known
            exact ⟨effect.trans lastEffect,retained.grows lastEffect.keeps,resident⟩

end MicroCFTA.SourceCurrentSharedParentProbeHeap
