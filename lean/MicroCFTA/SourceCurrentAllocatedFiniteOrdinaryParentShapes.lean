import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStageShapes
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardParent
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParentUniformNumbers

/-!
# Numeric profiles through actual local and parent reads

The actual own precheck bounds its literal class count and path depth.
The same stage reads derive rows without constructor headroom.
The parent uses its original arity and the Empty sentinel ceiling.
All stores and profiles refer to the supplied exact returned state.
No future body profile, range plan, or resource construction is an input.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParentShapes
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
local notation "Limits" => SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope.Limits
local notation "Bounds" => SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope.Bounds
local notation "NativeGuards" => SourceCurrentAllocatedFiniteOrdinaryGuardStored.Stored
local notation "MergeGuards" => SourceCurrentAllocatedFiniteOrdinaryMergeGuardCache.Stored
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

private theorem erased_shape (values : List (Value Symbol Guard)) (rows arity : Nat) :
    ChildrenShape rows arity (EqualityLeafProjectionRuntimeEmpty.erase values) := by
  unfold EqualityLeafProjectionRuntimeEmpty.erase
  induction values with
  | nil => trivial
  | cons value values ih => exact ⟨True.intro, ih⟩

variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem rejected_shape
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {before after : Checked width} {symbol : Symbol} {result : EdgeValue Symbol Guard}
    (receipt : SourceCurrentAllocatedMkEdge.RejectReceipt formulas solver inventory symbol before result after)
    (rows arity : Nat) : EdgeShape rows (max arity 1) result := by
  apply (show EdgeShape rows (max arity 1) result ↔
    result.children.length ≤ max arity 1 ∧ ChildrenShape rows (max arity 1) result.children from by cases result; rfl).mpr
  rw [receipt.children]
  exact ⟨Nat.le_max_right _ _, True.intro, True.intro⟩

private theorem constructor_shape
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {before after : Checked width} {symbol : Symbol} {loaded : Allocated}
    {children : List (Value Symbol Guard)} {result : EdgeValue Symbol Guard}
    (receipt : SourceCurrentAllocatedMkEdge.Receipt formulas solver inventory symbol loaded children before result after)
    (rows arity : Nat) (profile : ChildrenShape rows arity children) (lengthBound : children.length ≤ arity)
    (sentinel : 1 ≤ arity) : EdgeShape rows arity result := by
  apply (show EdgeShape rows arity result ↔
    result.children.length ≤ arity ∧ ChildrenShape rows arity result.children from by cases result; rfl).mpr
  rw [receipt.children]
  split
  · exact ⟨lengthBound, profile⟩
  · exact ⟨sentinel, True.intro, True.intro⟩

variable [DecidableEq Symbol] [DecidableEq (Value Symbol Guard)]

/-- Actual local reads derive row and arity bounds from their initial own guard vector. -/
theorem local_reads
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (original : Guard)
    {budget : Nat} {loaded : Allocated} {inherited : EqValue}
    {values results : List (Value Symbol Guard)} {before after : Checked width}
    {fourth savedFourth : Fourth} {memo saved : Memo} {memos final : Memos}
    {actual : SourceCurrentAllocatedLocalReduction.Reduction budget loaded inherited values before fourth memo results after savedFourth saved}
    (reads : SourceCurrentAllocatedLocalReductionActual.Reads formulas solver actual memos final)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (found : SourceEqualityConstraintFieldLookup.load original before.operations.constraints = .ok (some loaded))
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited)
    (available : Values before.native.machine.heap values)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (physicalStored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (native : NativeStored before.native) (profiles : Profiles memo) (output : OutputStored before.native)
    (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (limits : Limits) (ownBound : Bounds limits original)
    (rows arity count bound : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count) (heightBound : childrenHeight values ≤ bound) :
    NativeStored after.native ∧ OutputStored after.native ∧ Profiles saved ∧
      ChildrenShape (SourceCurrentAllocatedFiniteOrdinaryParentUniformNumbers.parentRows limits rows count bound)
        (max arity 1) results ∧ All₂ SourceCurrentAllocatedFiniteOrdinaryRequired.NodeNarrow values results ∧
      results.length = values.length ∧ childrenHeight results ≤ bound := by
  have domain := ChildrenShape.domain values profile
  cases reads with
  | unchanged =>
      exact ⟨native, output, profiles,
        ChildrenShape.mono _ profile (SourceCurrentAllocatedFiniteOrdinaryParentUniformNumbers.passRows_ge _ _ _ _ _ _)
          (Nat.le_max_left _ _),
        SourceCurrentAllocatedFiniteOrdinaryNarrow.forest_refl domain, rfl, heightBound⟩
  | emptyChildren =>
      have erased := erased_shape values
        (SourceCurrentAllocatedFiniteOrdinaryParentUniformNumbers.parentRows limits rows count bound) (max arity 1)
      exact ⟨native, output, profiles, erased, SourceCurrentAllocatedFiniteOrdinaryNarrow.forest_erase values,
        List.length_map _, Nat.le_trans (SourceCurrentAllocatedFiniteOrdinaryNarrow.forest_height
          (SourceCurrentAllocatedFiniteOrdinaryNarrow.forest_erase values)) heightBound⟩
  | classes read =>
      rename_i records outcome actual continuation
      obtain ⟨own, checked⟩ := SourceCurrentAllocatedLocalReductionActual.prefix_verified formulas solver inventory before
        original loaded inherited ready admitted cached found inheritedReady actual
      obtain ⟨proper, _, _, _, _, fields⟩ := checked.classes records rfl
      have recordsProper : ∀ record ∈ records, ∀ path ∈ record.paths, path ≠ [] := by
        intro record member
        exact proper record.paths (List.mem_map.mpr ⟨record, member, rfl⟩)
      have pathsBound := (SourceCurrentAllocatedFiniteOrdinaryGuardOwn.receipt checked limits ownBound).2.2.2
      have shaped := SourceCurrentAllocatedFiniteOrdinaryStageShapes.profile_from_reads formulas solver inventory read
        checked.ready checked.admitted available recordsProper fields correct physicalStored covered native profiles output valid
        rows arity count (SourceCurrentAllocatedFiniteOrdinaryGuardOwn.pathDepth limits) bound profile lengthBound pathsBound heightBound
      exact ⟨shaped.1, shaped.2.1, shaped.2.2.1,
        ChildrenShape.mono _ shaped.2.2.2.1
          (SourceCurrentAllocatedFiniteOrdinaryParentUniformNumbers.receipt_rows checked limits ownBound rows count bound)
          (SourceCurrentAllocatedFiniteOrdinaryParentUniformNumbers.pass_arity records arity),
        shaped.2.2.2.2.1, shaped.2.2.2.2.2.1, shaped.2.2.2.2.2.2⟩

/-- The same actual parent reads derive uniform numeric and hereditary guard profiles. -/
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
    (native : NativeStored before.native) (profiles : Profiles memo) (output : OutputStored before.native)
    (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (guards : NativeGuards before.native) (mergeGuards : MergeGuards memo)
    (rows arity bound : Nat) (shape : EdgeShape rows arity original) (heightBound : edgeHeight original ≤ bound) :
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
  have structural := SourceCurrentAllocatedFiniteOrdinaryParentProfiles.structure_from_reads formulas solver inventory original reads
    ready admitted live domain correct physicalStored covered native profiles output valid
  have guardBound := SourceCurrentAllocatedFiniteOrdinaryGuardParent.structure_from_reads formulas solver inventory original reads
    ready admitted live limits profile correct physicalStored covered native profiles.domain valid guards mergeGuards
  have shaped : EdgeShape (SourceCurrentAllocatedFiniteOrdinaryParentUniformNumbers.parentRows limits rows arity bound)
      (max arity 1) result := by
    cases reads with
    | rejected =>
        have constructor := SourceCurrentAllocatedMkEdge.reject_correct formulas solver inventory
          original.entry.key.symbol before ready admitted
        exact rejected_shape constructor _ _
    | live read =>
        rename_i children middle test built reduction
        obtain ⟨cached, found, inheritedReady, available⟩ := live test
        have localShape := local_reads formulas solver inventory original.entry.key.constraint read ready admitted
          cached found inheritedReady available correct physicalStored covered native profiles output valid limits
          (SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Edge.guard original profile)
          rows arity arity bound (EdgeShape.children original shape) (EdgeShape.arity original shape)
          (by simpa only [SourceCurrentAllocatedFiniteOrdinaryDomain.edgeHeight_children] using heightBound)
        obtain ⟨next, receipt⟩ := SourceCurrentAllocatedLocalReductionActual.verified formulas solver inventory
          original.entry.key.constraint read ready admitted cached found inheritedReady available correct physicalStored
          covered (ranges test) valid
        have loadedReady := SourceEqualityConstraintFieldLookup.load_ready original.entry.key.constraint
          before.operations.constraints ready.good.operations.constraints cached loaded found
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
        exact constructor_shape constructor _ _ localShape.2.2.2.1
          (by rw [localShape.2.2.2.2.2.1]; exact Nat.le_trans (EdgeShape.arity original shape) (Nat.le_max_left _ _))
          (Nat.le_max_right _ _)
  exact ⟨structural.1, structural.2.1, structural.2.2.1, guardBound.2.1, guardBound.2.2.1,
    shaped, guardBound.2.2.2.1, structural.2.2.2, Nat.le_trans structural.2.2.2.2 heightBound⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParentShapes
