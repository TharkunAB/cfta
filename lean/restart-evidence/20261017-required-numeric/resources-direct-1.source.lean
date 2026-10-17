import MicroCFTA.SourceCurrentConstrainedCapRequiredForecast
import MicroCFTA.SourceCurrentConstrainedCapGeneratedQueryResources
import MicroCFTA.SourceCurrentConjunctionClassScan

/-!
# Numeric heap transfers for actual Required requests

Heap bounds track the two issued counters and causal stored mass.
Required leaves the separate native domain supply unchanged. Literal input
widths bound actual constructors. Supported open Head uses WarmHead.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapRequiredResources
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedNativeResourceForecast (Profile Le)
open SourceCurrentConstrainedCapRequiredForecast (scalar constructorProfile headProfile)
open SourceEqualityRequiredSemanticCache (SemanticReady)
variable {Symbol Guard : Type}

/-- The current constructor heap fits the three physical profile components. -/
structure HeapFits (profile : Profile) (heap : State Symbol Guard) : Prop where
  /-- The issued node counter fits the profile. -/
  nodes : heap.nodes.next ≤ profile.nodes
  /-- The issued edge counter fits the profile. -/
  edges : heap.edges.next ≤ profile.edges
  /-- Each stored payload fits the causal mass bound. -/
  stored : InternedValueMassHeap.Stored profile.mass heap

/-- Larger component bounds retain the same constructor heap. -/
theorem HeapFits.mono {first last : Profile} {heap : State Symbol Guard}
    (fits : HeapFits first heap) (increase : Le first last) : HeapFits last heap :=
  ⟨Nat.le_trans fits.nodes increase.1, Nat.le_trans fits.edges increase.2.1,
    fits.stored.mono increase.2.2.2⟩

/-- The profile scalar bounds both issued counters and causal stored mass. -/
theorem HeapFits.scalar_fits {profile : Profile} {heap : State Symbol Guard}
    (fits : HeapFits profile heap) : SourceCurrentMemoMergeResourceControl.Fits (scalar profile) heap :=
  ⟨fits.stored.mono (SourceCurrentConstrainedCapTargetForecast.scalar_mass profile),
    Nat.le_trans fits.nodes (SourceCurrentConstrainedCapTargetForecast.scalar_nodes profile),
    Nat.le_trans fits.edges (SourceCurrentConstrainedCapTargetForecast.scalar_edges profile), Nat.zero_le _⟩

/-- The complete plan scalar supplies one common supported-reader ceiling. -/
def readFuel (profile : Profile) : Nat := SourceCurrentOpenRowReadResources.readFuel (scalar profile)

/-- Larger profiles retain the common supported-reader ceiling. -/
theorem readFuel_mono {first last : Profile} (increase : Le first last) : readFuel first ≤ readFuel last :=
  SourceCurrentOpenRowReadResources.readFuel_mono (SourceCurrentConstrainedCapEditForecast.scalar_mono increase)

/-- The complete mass of an available ordinary node bounds its literal row count. -/
theorem node_width {profile : Profile} {heap : State Symbol Guard} (fits : HeapFits profile heap)
    {entry rows depth free} (available : Available heap (.node entry rows depth free)) : rows.length ≤ scalar profile := by
  have mass := InternedValueMassHeap.available heap fits.stored _ available
  have count := InternedStoredEncodingWidth.edges_length rows
  have enough := SourceCurrentConstrainedCapTargetForecast.scalar_mass profile
  simp only [InternedValueMass.value] at mass
  omega

/-- A resident original edge bounds its literal child count before any child scan. -/
theorem edge_width {profile : Profile} {heap : State Symbol Guard} (fits : HeapFits profile heap)
    (edge : EdgeValue Symbol Guard) (resident : InternedEdgeResidency.EdgeResident heap edge) :
    edge.children.length ≤ scalar profile := by
  have mass := InternedValueMassHeap.resident heap fits.stored edge resident
  have count := InternedStoredEncodingWidth.values_length edge.children
  have enough := SourceCurrentConstrainedCapTargetForecast.scalar_mass profile
  simp only [InternedValueMass.edge] at mass
  omega

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Actual node construction fits the profile for its original row-count bound. -/
theorem node (profile : Profile) (count : Nat) (rows : List (EdgeValue Symbol Guard))
    (heap : State Symbol Guard) (fits : HeapFits profile heap) (resident : Edges heap rows)
    (length : rows.length ≤ count) : HeapFits (constructorProfile count profile) (run (makeNode rows) heap).2 := by
  have produced := SourceCurrentMemoMergeResourceControl.node rows heap (scalar profile) count fits.scalar_fits resident length
  exact ⟨produced.1.nodes, produced.1.edges, produced.1.stored⟩

/-- Actual raw edge construction fits the profile for its original child-count bound. -/
theorem edge (profile : Profile) (count : Nat) (symbol : Symbol) (guard : Guard)
    (values : List (Value Symbol Guard)) (heap : State Symbol Guard) (fits : HeapFits profile heap)
    (available : Values heap values) (length : values.length ≤ count) :
    HeapFits (constructorProfile count profile) (run (makeEdge symbol guard values) heap).2 := by
  have produced := SourceCurrentMemoMergeResourceControl.edge symbol guard values heap
    (scalar profile) count fits.scalar_fits available length
  exact ⟨produced.1.nodes, produced.1.edges, produced.1.stored⟩

/-- A supported actual open Head retains its exact heap profile and common read certificate. -/
theorem head (profile : Profile) {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : SourceEqualityRequiredHead.Head value before result after)
    (semantic : SemanticReady before) (costs : InternedFreshOrdinaryCostHeap.Heap before)
    (available : Available before value) (warm : SourceSecondaryGateHead.WarmHead before value)
    (fits : HeapFits profile before) :
    HeapFits (headProfile profile) after ∧
      SourceCurrentProjectionNumericReplay.HeadReady (readFuel (headProfile profile)) actual := by
  have produced := SourceCurrentOpenRowReadResources.head actual (scalar profile) semantic costs available warm fits.scalar_fits
  refine ⟨⟨produced.2.1.nodes, produced.2.1.edges, produced.2.1.stored⟩, ?_⟩
  simpa only [readFuel, headProfile, scalar, SourceCurrentConstrainedCapTargetForecast.scalar, Nat.max_self] using produced.2.2.2.2

local notation "CurrentSymbol" => SourceObservations.Label FullSyntax.Formula
local notation "CurrentGuard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "CheckedFits" => SourceCurrentConstrainedCapGeneratedQueryResources.Fits

/-- Initial checked-state bounds supply the physical constructor-heap bounds. -/
theorem of_checked {width : Nat} {profile : Profile} {before : Checked width}
    (fits : CheckedFits profile before) : HeapFits profile before.native.machine.heap :=
  ⟨fits.nodes, fits.edges, fits.stored⟩

/-- Actual Required heap growth retains the unchanged domain supply under the returned profile. -/
theorem to_checked {width : Nat} {first last : Profile} {before : Checked width}
    {heap : State CurrentSymbol CurrentGuard} (initial : CheckedFits first before)
    (increase : Le first last) (returned : HeapFits last heap) :
    CheckedFits last (SourceCurrentConjunctionClassScan.advanceHeap before heap) :=
  ⟨returned.nodes, returned.edges, Nat.le_trans initial.domains increase.2.2.1, returned.stored⟩

end MicroCFTA.SourceCurrentConstrainedCapRequiredResources
