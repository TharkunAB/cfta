import MicroCFTA.SourceCurrentOuterConstructorBounds

/-!
# Exact raw outer rebuild receipts in a uniform guard envelope

A resident original bounds its replacement width. Equal-length replacement
retains the original guard alphabet and the full query Frame. The numeric
bound uses the initial profile alone. These endpoints do not execute the
recursive child or row workers.
-/
namespace MicroCFTA.SourceCurrentOuterRebuildGuardAlphabet
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentConstrainedCapTargetForecast (scalar)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Known" => SourceEqualityAnnotationHeap.Heap
local notation "rawEdge" => SourceCurrentAllocatedRawRebuild.edge
local notation "rawModify" => SourceCurrentAllocatedRawRebuild.modify
local notation "uniform" => SourceCurrentOuterConstructorBounds.profile
variable {width : Nat}

private theorem edge_width (profile : Profile) (before : Checked width) (fits : Fits profile before)
    (original : Edge) (resident : EdgeResident before.native.machine.heap original) :
    original.children.length ≤ scalar profile := by
  have mass := InternedValueMassHeap.resident _ fits.stored original resident
  rw [InternedValueMass.edge_children, InternedValueMass.values_eq_length_sum] at mass
  have enough := SourceCurrentConstrainedCapTargetForecast.scalar_mass profile
  omega

private theorem node_width (profile : Profile) (before : Checked width) (fits : Fits profile before)
    (identity : Interned InternedBinderProtocol.NodeKey) (rows : List Edge) (depth : Nat)
    (free : List InternedBinderProtocol.Reference)
    (available : Available before.native.machine.heap (.node identity rows depth free)) :
    rows.length ≤ scalar profile := by
  have mass := InternedValueMassHeap.available _ fits.stored _ available
  simp only [InternedValueMass.value, InternedValueMass.edges_eq_length_sum] at mass
  have enough := SourceCurrentConstrainedCapTargetForecast.scalar_mass profile
  omega

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- The literal raw edge retains its full receipt, Frame, uniform profile, and initial carrier. -/
theorem edge (alphabet : List Guard) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (profile : Profile) (original : Edge) (children : List Node) (before : Checked width)
    (frame : Frame formulas solver inventory before) (fits : Fits profile before)
    (known : Known (fun guard => guard ∈ alphabet) before.native.machine.heap)
    (resident : EdgeResident before.native.machine.heap original)
    (available : Values before.native.machine.heap children) (same : children.length = original.children.length) :
    let actual := rawEdge original children before
    SourceCurrentAllocatedRawRebuild.EdgeReceipt formulas solver inventory original children before actual.1 actual.2 ∧
      Frame formulas solver inventory actual.2 ∧ Fits (uniform profile) actual.2 ∧
      Known (fun guard => guard ∈ alphabet) actual.2.native.machine.heap := by
  have built := SourceCurrentRawRebuildNumeric.edge formulas solver inventory original children before frame profile fits
    resident available same
  have length : children.length ≤ scalar profile := same ▸ edge_width profile before fits original resident
  have carrier := SourceEqualityAnnotationHeap.run (fun guard => guard ∈ alphabet)
    (makeEdge original.entry.key.symbol original.entry.key.constraint children)
    (SourceEqualityAnnotationHeap.makeEdge _ _ _ _ (known _ _ resident)) before.native.machine.heap known
  exact ⟨built.1, built.2.1, built.2.2.1.mono
    (SourceCurrentEditFrame.constructorProfile_count_mono length profile), carrier⟩

/-- Both literal node identity branches retain the full receipt and the same finite carrier. -/
theorem modify (alphabet : List Guard) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (profile : Profile) (identity : Interned InternedBinderProtocol.NodeKey)
    (oldRows newRows : List Edge) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (before : Checked width) (frame : Frame formulas solver inventory before) (fits : Fits profile before)
    (known : Known (fun guard => guard ∈ alphabet) before.native.machine.heap)
    (available : Available before.native.machine.heap (.node identity oldRows depth free))
    (resident : Edges before.native.machine.heap newRows) (sameLength : newRows.length = oldRows.length) :
    let original := Value.node identity oldRows depth free
    let actual := rawModify original oldRows newRows before
    SourceCurrentAllocatedRawRebuild.NodeReceipt formulas solver inventory original oldRows newRows before actual.1 actual.2 ∧
      Frame formulas solver inventory actual.2 ∧ Fits (uniform profile) actual.2 ∧
      Known (fun guard => guard ∈ alphabet) actual.2.native.machine.heap := by
  have built := SourceCurrentRawRebuildNumeric.modify formulas solver inventory identity oldRows newRows depth free before
    frame profile fits available resident
  have length : newRows.length ≤ scalar profile := sameLength ▸ node_width profile before fits identity oldRows depth free available
  refine ⟨built.1, built.2.1, built.2.2.1.mono
    (SourceCurrentEditFrame.constructorProfile_count_mono length profile), ?_⟩
  by_cases same : newRows.map (fun row => row.entry.identity) = oldRows.map (fun row => row.entry.identity)
  · simpa only [SourceCurrentAllocatedRawRebuild.modify_unchanged _ _ _ _ same] using known
  · simpa only [SourceCurrentAllocatedRawRebuild.modify, SourceEqualityPartialNodeRebuild.modify, same, ↓reduceIte,
      SourceEqualityNativeScoped.advanceHeap, SourceRecursiveIntersectionThunks.advance,
      SourceCurrentAllocatedQueryMemo.advancePhysical] using
        SourceEqualityAnnotationHeap.run (fun guard => guard ∈ alphabet) (makeNode newRows)
          (SourceEqualityAnnotationHeap.makeNode _ _) before.native.machine.heap known

end MicroCFTA.SourceCurrentOuterRebuildGuardAlphabet
