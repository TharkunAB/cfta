import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardLocal

/-!
# Hereditary guards through actual parent edge reads

The live parent uses the actual local return and full raw stored guard.
The constructor retains native cells and can choose the Top sentinel.
The rejected branch has no premise about available or evaluated children.
The initial own guard vector bounds all local class steps.
No future guard profile, range plan, or completed body is an input.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardParent
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
variable {width : Nat}

/-- One parent uses its own initial vector for both the guard and its forest. -/
def outputLimit (limits : Limits) : Limits :=
  SourceCurrentAllocatedFiniteOrdinaryGuardLocal.outputLimit limits limits

private theorem constructor_guards
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {before after : Checked width} {result : EdgeValue Symbol Guard}
    (receipt : SourceCurrentAllocatedMkEdge.PhysicalReceipt formulas solver inventory before result after)
    (guards : NativeGuards before.native) : NativeGuards after.native :=
  ⟨by simpa only [receipt.nodes] using guards.nodes, by simpa only [receipt.edges] using guards.edges⟩

variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem constructor_profile
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {before after : Checked width} {symbol : Symbol} {loaded : Allocated}
    {children : List (Value Symbol Guard)} {result : EdgeValue Symbol Guard}
    (receipt : SourceCurrentAllocatedMkEdge.Receipt formulas solver inventory symbol loaded children before result after)
    (limits : Limits) (guard : Bounds limits (raw loaded)) (profile : Children limits children) :
    SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Edge limits result := by
  have selectedGuard := receipt.guard
  have selectedChildren := receipt.children
  cases selected : SourceEqualityMkEdgeAllocation.accepted (raw loaded) children.length with
  | true =>
      simp only [selected, ↓reduceIte] at selectedGuard selectedChildren
      cases result
      simp only [EdgeValue.entry, EdgeValue.children] at selectedGuard selectedChildren
      constructor
      · rw [selectedGuard]
        exact guard
      · rw [selectedChildren]
        exact profile
  | false =>
      simp only [selected, Bool.false_eq_true, ↓reduceIte] at selectedGuard selectedChildren
      cases result
      simp only [EdgeValue.entry, EdgeValue.children] at selectedGuard selectedChildren
      constructor
      · rw [selectedGuard]
        exact SourceCurrentAllocatedFiniteOrdinaryGuardLimits.top_bounds limits
      · rw [selectedChildren]
        exact ⟨True.intro, True.intro⟩

private theorem rejected_profile
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {before after : Checked width} {symbol : Symbol} {result : EdgeValue Symbol Guard}
    (receipt : SourceCurrentAllocatedMkEdge.RejectReceipt formulas solver inventory symbol before result after)
    (limits : Limits) : SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Edge limits result := by
  have selectedGuard := receipt.guard
  have selectedChildren := receipt.children
  cases result
  simp only [EdgeValue.entry, EdgeValue.children] at selectedGuard selectedChildren
  constructor
  · rw [selectedGuard]
    exact SourceCurrentAllocatedFiniteOrdinaryGuardLimits.top_bounds limits
  · rw [selectedChildren]
    exact ⟨True.intro, True.intro⟩

variable [DecidableEq Symbol] [DecidableEq (Value Symbol Guard)]

/-- Supplied parent reads derive hereditary output guards and retain both universal stores. -/
theorem structure_from_reads
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
    (native : NativeStored before.native) (merged : MergeStored memo)
    (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (guards : NativeGuards before.native) (mergeGuards : MergeGuards memo) :
    NativeStored after.native ∧ NativeGuards after.native ∧ MergeGuards saved ∧
      SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Edge (outputLimit limits) result ∧
      SourceCurrentAllocatedFiniteOrdinaryRequired.EdgeNarrow original result := by
  have domain := SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Edge.domain original profile
  have ranges : ∀ test : contradictory original.entry.key.constraint = false,
      SourceCurrentAllocatedLocalReductionActual.Ranges budget loaded inherited original.children before fourth := by
    intro test records _
    exact SourceCurrentAllocatedFiniteOrdinaryScanRanges.scan_ranges budget sourceGate sourceReaches original.children
      (records.map SourceEqualityClassOrder.Record.paths) (SourceCurrentAllocatedPrecheck.state before loaded inherited) fourth
      ready.good.native.machine.1.coherent (live test).2.2.2 domain
  have structural := SourceCurrentAllocatedFiniteOrdinaryParent.structure_from_reads formulas solver inventory original reads
    ready admitted (fun test => ⟨(live test).1, (live test).2.1, (live test).2.2.1, (live test).2.2.2, ranges test⟩)
    domain correct physicalStored covered native merged valid
  have retained : MergeGuards saved ∧ NativeGuards after.native ∧
      SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Edge (outputLimit limits) result := by
    cases reads with
    | rejected =>
        have constructor := SourceCurrentAllocatedMkEdge.reject_correct formulas solver inventory
          original.entry.key.symbol before ready admitted
        exact ⟨mergeGuards, constructor_guards constructor.toPhysicalReceipt guards, rejected_profile constructor _⟩
    | live reads =>
        rename_i children middle test built reduction
        obtain ⟨cached, found, inheritedReady, available⟩ := live test
        have loadedReady := SourceEqualityConstraintFieldLookup.load_ready original.entry.key.constraint
          before.operations.constraints ready.good.operations.constraints cached loaded found
        have retained := SourceCurrentAllocatedFiniteOrdinaryGuardLocal.local_reads formulas solver inventory
          original.entry.key.constraint reads ready admitted cached found inheritedReady available
          correct physicalStored covered native merged valid guards mergeGuards limits limits
          (SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Edge.guard original profile)
          (SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Edge.children original profile)
        obtain ⟨next, receipt⟩ := SourceCurrentAllocatedLocalReductionActual.verified formulas solver inventory
          original.entry.key.constraint reads ready admitted cached found inheritedReady available correct physicalStored
          covered (ranges test) valid
        have storedReady := loadedReady.1.grows receipt.effects.grows.constraint_growth
        have field : SourceCurrentConjunctionEquality.FieldAvailable middle.operations (raw loaded) := by
          rw [loadedReady.2]
          exact (show SourceCurrentConjunctionEquality.FieldAvailable before.operations original.entry.key.constraint from
            ⟨cached, loaded, found⟩).grows receipt.effects.grows
        obtain ⟨chosen, returned, constructor⟩ := SourceCurrentAllocatedMkEdge.finite formulas solver next
          original.entry.key.symbol loaded children middle receipt.ready receipt.admitted storedReady field receipt.available
        have same := Prod.mk.inj (constructor.actual.symm.trans built)
        have sameValue := Except.ok.inj same.1
        cases sameValue
        cases same.2
        have rawBound : Bounds (outputLimit limits) (raw loaded) := by
          rw [loadedReady.2]
          exact SourceCurrentAllocatedFiniteOrdinaryGuardLimits.bounds_mono _
            (SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Edge.guard original profile)
            (SourceCurrentAllocatedFiniteOrdinaryGuardTarget.foldLimit_ge _ _)
        exact ⟨retained.1, constructor_guards constructor.toPhysicalReceipt retained.2.1,
          constructor_profile constructor _ rawBound retained.2.2⟩
  exact ⟨structural.1, retained.2.1, retained.1, retained.2.2, structural.2.2⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardParent
