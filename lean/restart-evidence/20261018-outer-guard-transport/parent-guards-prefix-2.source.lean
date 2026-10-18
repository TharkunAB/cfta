import MicroCFTA.SourceCurrentNativeGuardHeapReturns
import MicroCFTA.SourceCurrentParentOperationInvariants
import MicroCFTA.SourceCurrentGateGuard
import MicroCFTA.SourceCurrentConjunctionGuard
import MicroCFTA.SourceCurrentRequiredGuard

/-!
# Causal guard heaps through literal successful Parent workers

Actual successful worker equations expose the reached stages. Existing
physical effects derive the intermediate inputs. Each stage retains the
same arbitrary body-to-probe guard predicate. No future guard heap, Cap,
closed forest, reached range, or completed call graph is an input.
These theorems do not construct general Parent or outer completion.
-/
namespace MicroCFTA.SourceCurrentParentGuardHeapReturns
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentNativeOperationHeap (Good)
open SourceCurrentLowerOperationInvariants (Effect)
open SourceCurrentMemoMergeEffects (Stored)
open SourceCurrentConstrainedCapGuardHeap (Heap)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "FieldAvailable" => SourceCurrentConjunctionEquality.FieldAvailable
variable {width : Nat}

private theorem seeded_operand (annotation : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)]
    {p h path values before result after}
    (actual : SourceCurrentAllocatedSeededWorker.operand p h path values before = .done result after)
    (good : Good (width := width) before) (available : Values before.native.machine.heap values)
    (guards : Heap annotation before.native.machine.heap) : Heap annotation after.native.machine.heap := by
  cases observed : SourceEqualityProjectionWorker.forest p h path values before.native.machine.heap with
  | pending | unresolved | exhausted => simp only [SourceCurrentAllocatedSeededWorker.operand,observed] at actual; cases actual
  | done value heap =>
    simp only [SourceCurrentAllocatedSeededWorker.operand,observed] at actual
    cases actual
    exact SourceCurrentConstrainedCapProjectionGuard.forest annotation
      (SourceEqualityProjectionWorkerSound.forest_graph _ _ _ _ _ _ _ observed)
      good.semantic good.costs available guards

private theorem seeded_bind_done
    (first : SourceCurrentAllocatedSeededWorker.Outcome width)
    (next : Node → Checked width → SourceCurrentAllocatedSeededWorker.Outcome width)
    {output : Node} {after : Checked width} (actual : first.bind next = .done output after) :
    ∃ value middle, first = .done value middle ∧ next value middle = .done output after := by
  cases first with
  | done value middle => exact ⟨value,middle,rfl,actual⟩
  | failed => cases actual

private theorem seeded_leaf (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {n left right before result after}
    (actual : SourceCurrentAllocatedSeededWorker.leaf n left right before = .done result after)
    (good : Good (width := width) before) (first : Available before.native.machine.heap left)
    (second : Available before.native.machine.heap right)
    (guards : Heap annotation before.native.machine.heap) : Heap annotation after.native.machine.heap := by
  cases observed : SourceEqualityNativeDemand.execute n
      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) before with
  | yielded | failed | constraintError | blocked => simp only [SourceCurrentAllocatedSeededWorker.leaf,observed] at actual; cases actual
  | done value checked =>
    simp only [SourceCurrentAllocatedSeededWorker.leaf,observed] at actual
    cases actual
    exact SourceCurrentNativeGuardHeapReturns.node annotation n _ before after result good guards
      ⟨SourceRecursiveIntersectionKernel.empty_domain before.native.machine,first,second⟩ observed

private theorem seeded_fold (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {p h n values seed paths before result after}
    (actual : SourceCurrentAllocatedSeededWorker.fold p h n values seed paths before = .done result after)
    (good : Good (width := width) before) (available : Values before.native.machine.heap values)
    (guards : Heap annotation before.native.machine.heap) : Heap annotation after.native.machine.heap := by
  induction paths generalizing before result after with
  | nil => exact seeded_operand annotation actual good available guards
  | cons path paths ih =>
    obtain ⟨head,middle,first,later⟩ := seeded_bind_done _ _ actual
    have firstDone : SourceCurrentAllocatedSeededWorker.seeded p h n values [path] before = .done head middle := first
    obtain ⟨headEffect,known⟩ := SourceCurrentParentOperationInvariants.seeded firstDone good available
    have middleAvailable := fun value member => headEffect.keeps.available value (available value member)
    obtain ⟨tail,final,rest,last⟩ := seeded_bind_done _ _ later
    have restDone : SourceCurrentAllocatedSeededWorker.seeded p h n values (seed :: paths) middle = .done tail final := rest
    obtain ⟨tailEffect,tailKnown⟩ := SourceCurrentParentOperationInvariants.seeded restDone headEffect.good middleAvailable
    have tailGuards := ih rest headEffect.good middleAvailable (seeded_operand annotation first good available guards)
    exact seeded_leaf annotation last tailEffect.good (tailEffect.keeps.available _ known) tailKnown tailGuards

/-- A completed seeded query retains arbitrary causal guard observations from its initial inputs. -/
theorem seeded (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {p h n values paths before result after}
    (actual : SourceCurrentAllocatedSeededWorker.seeded p h n values paths before = .done result after)
    (good : Good (width := width) before) (available : Values before.native.machine.heap values)
    (guards : Heap annotation before.native.machine.heap) : Heap annotation after.native.machine.heap := by
  cases paths with
  | nil => cases actual; exact guards
  | cons seed paths => exact seeded_fold annotation actual good available guards

private theorem gate (annotation : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)]
    {below fuel values paths before fourth answer after saved}
    (actual : SourceCurrentAllocatedScanWorker.gate below fuel values paths before fourth = .done answer after saved)
    (good : Good (width := width) before) (available : Values before.native.machine.heap values)
    (guards : Heap annotation before.native.machine.heap) : Effect before after ∧ Heap annotation after.native.machine.heap := by
  cases below with
  | true =>
    cases observed : SourceCurrentAllocatedGateWorker.primary fuel values paths before with
    | failed => simp only [SourceCurrentAllocatedScanWorker.gate,ite_true,observed] at actual; cases actual
    | done value checked =>
      simp only [SourceCurrentAllocatedScanWorker.gate,ite_true,observed] at actual
      cases actual
      have graph := SourceCurrentAllocatedGateWorker.primary_graph observed
      have effects := SourceCurrentAllocatedGateFields.primary_class _ _ graph good.physical available
      have same := (SourceCurrentAllocatedGateWorker.primary_done observed).2
      have effect : Effect before after := same.symm ▸
        (⟨good.advance _ effects.1,effects.1.keeps,effects.1.grows⟩ : Effect before (SourceCurrentConjunctionClassScan.advanceHeap before after.native.machine.heap))
      exact ⟨effect,SourceCurrentGateGuard.primary annotation _ _ graph good.semantic good.costs available guards⟩
  | false =>
    cases observed : SourceCurrentAllocatedGateWorker.secondary fuel values paths before with
    | failed => simp only [SourceCurrentAllocatedScanWorker.gate,Bool.false_eq_true,ite_false,observed] at actual; cases actual
    | done value checked =>
      simp only [SourceCurrentAllocatedScanWorker.gate,Bool.false_eq_true,ite_false,observed] at actual
      cases actual
      have graph := SourceCurrentAllocatedGateWorker.secondary_graph observed
      have effects := SourceCurrentAllocatedGateFields.secondary_class _ graph good.physical available
      have same := (SourceCurrentAllocatedGateWorker.secondary_done observed).2
      have effect : Effect before after := same.symm ▸
        (⟨good.advance _ effects.1,effects.1.keeps,effects.1.grows⟩ : Effect before (SourceCurrentConjunctionClassScan.advanceHeap before after.native.machine.heap))
      exact ⟨effect,SourceCurrentGateGuard.secondary annotation _ graph good.semantic good.costs available guards⟩

private theorem scan_bind_done {A B : Type}
    (first : SourceCurrentAllocatedScanWorker.Outcome A width)
    (next : A → Checked width → Fourth → SourceCurrentAllocatedScanWorker.Outcome B width)
    {output : B} {after : Checked width} {saved : Fourth} (actual : first.bind next = .done output after saved) :
    ∃ value middle current, first = .done value middle current ∧ next value middle current = .done output after saved := by
  cases first with
  | done value middle current => exact ⟨value,middle,current,rfl,actual⟩
  | failed => cases actual

private theorem scan_query (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {p h n values paths before fourth result after saved}
    (actual : SourceCurrentAllocatedScanWorker.query p h n values paths before fourth = .done result after saved)
    (good : Good (width := width) before) (available : Values before.native.machine.heap values)
    (guards : Heap annotation before.native.machine.heap) :
    Effect before after ∧ Available after.native.machine.heap result ∧ Heap annotation after.native.machine.heap := by
  cases observed : SourceCurrentAllocatedSeededWorker.seeded p h n values (paths.map (List.map Int.ofNat)) before with
  | failed => simp only [SourceCurrentAllocatedScanWorker.query,observed] at actual; cases actual
  | done value checked =>
    simp only [SourceCurrentAllocatedScanWorker.query,observed] at actual
    cases actual
    have effect := SourceCurrentParentOperationInvariants.seeded observed good available
    exact ⟨effect.1,effect.2,seeded annotation observed good available guards⟩

private theorem scan_decision (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
    {p h budget paths value before fourth answer after saved}
    (actual : SourceCurrentAllocatedScanWorker.decision p h budget paths value before fourth = .done answer after saved)
    (good : Good (width := width) before) (available : Available before.native.machine.heap value)
    (guards : Heap annotation before.native.machine.heap) : Effect before after ∧ Heap annotation after.native.machine.heap := by
  cases observed : SourceCurrentAllocatedConjunctionWorker.call p h budget value before fourth with
  | failed => simp only [SourceCurrentAllocatedScanWorker.decision,observed] at actual; cases actual
  | done result checked current =>
    simp only [SourceCurrentAllocatedScanWorker.decision,observed] at actual
    cases actual
    obtain ⟨heap,done,rfl⟩ := SourceCurrentAllocatedConjunctionWorker.call_done observed
    have graph := SourceCurrentConjunctionWorkerCompletion.call_sound p h budget fourth value (physical before) _ heap _ done
    obtain ⟨answer,heap,saved,produced,effects⟩ := SourceCurrentConjunctionMemo.complete budget fourth value (physical before) good.physical available
    obtain ⟨_,rfl,_⟩ := SourceCurrentConjunctionCallUnique.call graph produced
    exact ⟨⟨good.advance _ effects,effects.keeps,effects.grows⟩,
      SourceCurrentConjunctionGuard.call annotation graph good.physical available guards⟩

/-- Every reached successful Scan branch retains the initial causal guard heap. -/
theorem scan (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
    {g s p h n budget values classes before fourth result after saved}
    (actual : SourceCurrentAllocatedScanWorker.scan g s p h n budget values classes before fourth = .done result after saved)
    (good : Good (width := width) before) (available : Values before.native.machine.heap values)
    (guards : Heap annotation before.native.machine.heap) : Heap annotation after.native.machine.heap := by
  induction classes generalizing before fourth result after saved with
  | nil => cases actual; exact guards
  | cons paths classes ih =>
    obtain ⟨primary,middle,current,first,later⟩ := scan_bind_done _ _ actual
    obtain ⟨firstEffect,firstGuards⟩ := gate annotation first good available guards
    have middleAvailable := fun value member => firstEffect.keeps.available value (available value member)
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
          exact ih observed firstEffect.good middleAvailable firstGuards
    | true =>
      simp only [ite_true] at later
      obtain ⟨secondary,last,completed,second,later⟩ := scan_bind_done _ _ later
      obtain ⟨secondEffect,secondGuards⟩ := gate annotation second firstEffect.good middleAvailable firstGuards
      have prefixEffect := firstEffect.trans secondEffect
      have lastAvailable := fun value member => prefixEffect.keeps.available value (available value member)
      cases secondary with
      | true =>
        simp only [ite_true] at later
        exact ih later secondEffect.good lastAvailable secondGuards
      | false =>
        simp only [Bool.false_eq_true,ite_false] at later
        obtain ⟨value,queried,next,queryDone,later⟩ := scan_bind_done _ _ later
        obtain ⟨queryEffect,known,queryGuards⟩ := scan_query annotation queryDone secondEffect.good lastAvailable secondGuards
        obtain ⟨answer,decided,final,decisionDone,later⟩ := scan_bind_done _ _ later
        obtain ⟨decisionEffect,decisionGuards⟩ := scan_decision annotation decisionDone queryEffect.good known queryGuards
        have prefixEffect := (prefixEffect.trans queryEffect).trans decisionEffect
        cases answer with
        | true => cases later; exact decisionGuards
        | false =>
          simp only [Bool.false_eq_true,ite_false] at later
          exact ih later decisionEffect.good
            (fun value member => prefixEffect.keeps.available value (available value member)) decisionGuards

private theorem local_bind_done {A B : Type}
    (first : SourceCurrentAllocatedLocalWorker.Outcome A width)
    (next : A → Checked width → Fourth → Memo → SourceCurrentAllocatedLocalWorker.Outcome B width)
    {output : B} {after : Checked width} {fourth : Fourth} {saved : Memo}
    (actual : first.bind next = .done output after fourth saved) :
    ∃ value middle current memo, first = .done value middle current memo ∧ next value middle current memo = .done output after fourth saved := by
  cases first with
  | done value middle current memo => exact ⟨value,middle,current,memo,rfl,actual⟩
  | failed => cases actual

private theorem local_scan (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
    {g s p h n budget records values before fourth memo result after saved current}
    (actual : SourceCurrentAllocatedLocalWorker.scan g s p h n budget records values before fourth memo = .done result after saved current)
    (good : Good (width := width) before) (available : Values before.native.machine.heap values)
    (guards : Heap annotation before.native.machine.heap) :
    Effect before after ∧ current = memo ∧ Heap annotation after.native.machine.heap := by
  cases observed : SourceCurrentAllocatedRecordScanWorker.scan g s p h n budget values records before fourth with
  | failed => simp only [SourceCurrentAllocatedLocalWorker.scan,observed] at actual; cases actual
  | done output checked completed =>
    simp only [SourceCurrentAllocatedLocalWorker.scan,observed] at actual
    cases actual
    have paths := (SourceCurrentAllocatedRecordScanWorker.scan_mapPaths g s p h n budget values records before fourth).symm
    rw [observed] at paths
    exact ⟨SourceCurrentParentOperationInvariants.scan paths good available,rfl,scan annotation paths good available guards⟩

private theorem local_required (annotation : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)]
    {r h paths values before fourth memo results after saved current}
    (actual : SourceCurrentAllocatedLocalWorker.required r h paths values before fourth memo = .done results after saved current)
    (good : Good (width := width) before) (available : Values before.native.machine.heap values)
    (guards : Heap annotation before.native.machine.heap) :
    Effect before after ∧ Values after.native.machine.heap results ∧ current = memo ∧ Heap annotation after.native.machine.heap := by
  cases observed : SourceEqualityRequiredExecution.requireAll r h paths values before.native.machine.heap with
  | pending | unresolved | exhausted => simp only [SourceCurrentAllocatedLocalWorker.required,observed] at actual; cases actual
  | done output heap =>
    simp only [SourceCurrentAllocatedLocalWorker.required,observed] at actual
    cases actual
    obtain ⟨keeps,semantic,costs,fields,known⟩ := SourceCurrentRequiredHeapEffects.requireAll
      (FieldAvailable before.operations) r h paths values _ _ heap observed good.semantic good.costs good.fields available
    have effects : SourceCurrentConjunctionRowsAllocation.Effects (physical before) ⟨heap,before.operations⟩ :=
      ⟨keeps,⟨semantic,costs,good.operations,fields⟩,SourceEqualityConstraintMemoAllocation.grows_refl _⟩
    have graph := (SourceEqualityRequiredExecution.requireAll_execution_iff paths values _ results heap).mpr ⟨r,h,observed⟩
    cases compiled : SourceEqualityNeeded.build paths with
    | node entries =>
      simp only [compiled] at graph
      exact ⟨⟨good.advance _ effects,keeps,effects.grows⟩,known,rfl,
        SourceCurrentRequiredGuard.children annotation graph good.semantic good.costs available guards⟩


end MicroCFTA.SourceCurrentParentGuardHeapReturns
