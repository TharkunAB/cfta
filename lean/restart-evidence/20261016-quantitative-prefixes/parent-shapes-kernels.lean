import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParentShapes
set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option format.width 200

namespace MicroCFTA.ParentShapesIntegration
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan (Ready advanceHeap)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "DChildren" => SourceCurrentAllocatedFiniteOrdinaryDomain.Children
local notation "DEdge" => SourceCurrentAllocatedFiniteOrdinaryDomain.Edge
local notation "Limits" => SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope.Limits
local notation "Bounds" => SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope.Bounds
local notation "Children" => SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Children
local notation "NativeGuards" => SourceCurrentAllocatedFiniteOrdinaryGuardStored.Stored
local notation "MergeGuards" => SourceCurrentAllocatedFiniteOrdinaryMergeGuardCache.Stored
local notation "MergeStored" => SourceCurrentAllocatedFiniteOrdinaryMergeCache.Stored
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "sourceGate" => SourceMemoGate.unconstrained
local notation "sourceReaches" => SourceEndpointReachability.reaches sourceGate
local notation "contradictory" => SourceEqualityMkEdgeAllocation.contradictory
local notation "raw" => SourceEqualityConjoinAllocation.readback
local notation "OutputStored" => SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored
local notation "Profiles" => SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (ChildrenShape EdgeShape)
open MergedOrdinaryHeight (childrenHeight edgeHeight)
variable {width : Nat}


variable [DecidableEq (EdgeKey Symbol Guard)]

variable [DecidableEq Symbol] [DecidableEq (Value Symbol Guard)]

theorem actual_parent_receipt_shapes_and_guards
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (original : EdgeValue Symbol Guard)
    {budget : Nat} {loaded : Allocated} {inherited : EqValue}
    {before after : Checked width} {result : EdgeValue Symbol Guard}
    {fourth savedFourth : Fourth} {memo saved : Memo} {memos final : Memos}
    {actual : SourceCurrentAllocatedParentEdge.Edge budget original.entry.key.symbol original.entry.key.constraint
      loaded inherited original.children before fourth memo result after savedFourth saved}
    (reads : SourceCurrentAllocatedParentEdgeActual.Reads formulas solver actual memos final)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (live : contradictory original.entry.key.constraint = false →
      SourceEqualityGuardReadback.Cached original.entry.key.constraint.equalities ∧
      SourceEqualityConstraintFieldLookup.load original.entry.key.constraint before.operations.constraints = .ok (some loaded) ∧
      SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited ∧
      Values before.native.machine.heap original.children)
    (limits : Limits) (profile : SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Edge limits original)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (physicalStored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (native : NativeStored before.native) (profiles : Profiles memo) (output : OutputStored before.native)
    (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (guards : NativeGuards before.native) (mergeGuards : MergeGuards memo)
    (rows arity bound : Nat) (shape : EdgeShape rows arity original) (heightBound : edgeHeight original ≤ bound) :
    ∃ next, SourceCurrentAllocatedParentEdge.Receipt formulas solver next original.entry.key.symbol
      original.entry.key.constraint loaded inherited original.children before result after fourth savedFourth memo saved final ∧
      NativeStored after.native ∧ OutputStored after.native ∧ Profiles saved ∧
      NativeGuards after.native ∧ MergeGuards saved ∧
      EdgeShape (SourceCurrentAllocatedFiniteOrdinaryParentUniformNumbers.parentRows limits rows arity bound) (max arity 1) result ∧
      SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Edge (SourceCurrentAllocatedFiniteOrdinaryGuardParent.outputLimit limits) result ∧
      SourceCurrentAllocatedFiniteOrdinaryRequired.EdgeNarrow original result ∧ edgeHeight result ≤ bound := by
  have domain := SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Edge.domain original profile
  have ranges : ∀ test : contradictory original.entry.key.constraint = false,
      SourceCurrentAllocatedLocalReductionActual.Ranges budget loaded inherited original.children before fourth := by
    intro test records _
    exact SourceCurrentAllocatedFiniteOrdinaryScanRanges.scan_ranges budget sourceGate sourceReaches original.children
      (records.map SourceEqualityClassOrder.Record.paths) (SourceCurrentAllocatedPrecheck.state before loaded inherited) fourth
      ready.good.native.machine.1.coherent (live test).2.2.2 domain
  obtain ⟨next, receipt⟩ := SourceCurrentAllocatedParentEdgeActual.verified formulas solver inventory reads ready admitted
    (fun test => ⟨(live test).1, (live test).2.1, (live test).2.2.1, (live test).2.2.2, ranges test⟩)
    correct physicalStored covered valid
  exact ⟨next, receipt, SourceCurrentAllocatedFiniteOrdinaryParentShapes.structure_from_reads formulas solver inventory original
    reads ready admitted live limits profile correct physicalStored covered native profiles output valid guards mergeGuards
    rows arity bound shape heightBound⟩

/-- Raw contradiction constructs its exact sentinel graph and numeric/guard profiles without child demand. -/
theorem rejected_parent_shapes
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (original : EdgeValue Symbol Guard) (loaded : Allocated) (inherited : EqValue)
    (before : Checked width) (fourth : Fourth) (memo : Memo) (memos : Memos)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (test : contradictory original.entry.key.constraint = true)
    (limits : Limits) (profile : SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Edge limits original)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (physical : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (native : NativeStored before.native) (profiles : Profiles memo) (output : OutputStored before.native)
    (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (guards : NativeGuards before.native) (mergeGuards : MergeGuards memo)
    (rows arity bound : Nat) (shape : EdgeShape rows arity original) (heightBound : edgeHeight original ≤ bound) :
    let result := (SourceCurrentAllocatedMkEdge.reject original.entry.key.symbol before).1
    let after := (SourceCurrentAllocatedMkEdge.reject original.entry.key.symbol before).2
    ∃ actual : SourceCurrentAllocatedParentEdge.Edge budget original.entry.key.symbol original.entry.key.constraint
      loaded inherited original.children before fourth memo result after fourth memo,
      SourceCurrentAllocatedParentEdgeActual.Reads formulas solver actual memos memos ∧
      EdgeShape (SourceCurrentAllocatedFiniteOrdinaryParentUniformNumbers.parentRows limits rows arity bound) (max arity 1) result ∧
      SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Edge (SourceCurrentAllocatedFiniteOrdinaryGuardParent.outputLimit limits) result ∧
      result.entry.key.constraint = SourceEqualityConstraintConstructors.top ∧ result.children = [.empty] ∧
      NativeGuards after.native ∧ MergeGuards memo := by
  let actual : SourceCurrentAllocatedParentEdge.Edge budget original.entry.key.symbol original.entry.key.constraint
      loaded inherited original.children before fourth memo _ _ fourth memo := .rejected test
  have reads : SourceCurrentAllocatedParentEdgeActual.Reads formulas solver actual memos memos := .rejected (test := test)
  have checked := SourceCurrentAllocatedFiniteOrdinaryParentShapes.structure_from_reads formulas solver inventory original
    reads ready admitted (fun impossible => by rw [test] at impossible; cases impossible)
    limits profile correct physical covered native profiles output valid guards mergeGuards rows arity bound shape heightBound
  have constructor := SourceCurrentAllocatedMkEdge.reject_correct formulas solver inventory original.entry.key.symbol before ready admitted
  exact ⟨actual, reads, checked.2.2.2.2.2.1, checked.2.2.2.2.2.2.1,
    constructor.guard, constructor.children, checked.2.2.2.1, checked.2.2.2.2.1⟩

end MicroCFTA.ParentShapesIntegration

#print axioms MicroCFTA.ParentShapesIntegration.actual_parent_receipt_shapes_and_guards
#check @MicroCFTA.ParentShapesIntegration.actual_parent_receipt_shapes_and_guards
#print axioms MicroCFTA.ParentShapesIntegration.rejected_parent_shapes
#check @MicroCFTA.ParentShapesIntegration.rejected_parent_shapes
