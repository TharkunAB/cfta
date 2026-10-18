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

private theorem seeded_bind_done {A : Type}
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

private theorem scan_query [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
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

end MicroCFTA.SourceCurrentParentOperationInvariants
