import MicroCFTA.SourcePruningEnumerationCostBounds
import MicroCFTA.SourcePruningEnumerationGuardWidth
import MicroCFTA.SourceCurrentConstrainedCapRequiredResources
import MicroCFTA.SourceEqualityAnnotationHeap

/-!
# An original bound for an ordinary alternative scan

The initial profile bounds row and child counts. The initial guard alphabet
bounds projected equality classes. The selector retains stored edges and
does not increase their count. Duplicate selected entries remain counted.
-/
namespace MicroCFTA.SourcePruningEnumerationOriginalForecast
open EnumerationState InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationIncomingReservation (Seed)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "scalar" => SourceCurrentConstrainedCapTargetForecast.scalar

/-- Bound the full scan from the original profile, alphabet and inherited bucket length. -/
noncomputable def count (seed : Seed) (inherited : Nat) : Nat :=
  scalar seed.2 * scalar seed.2 * (inherited + SourcePruningEnumerationGuardWidth.width seed.1 + 1)

/-- Current heap facts derive the exact scan cost below the original bound. -/
theorem cost_le (seed : Seed) (inherited : Nat)
    (heap : State Symbol Constraint)
    (bounded : SourceCurrentConstrainedCapRequiredResources.HeapFits seed.2 heap)
    (known : Heap (fun guard => guard ∈ seed.1) heap)
    (linked : InternedEdgeResidency.Linked heap)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey)
    (stored selected : List (EdgeValue Symbol Constraint)) (depth : Nat)
    (free : List InternedBinderProtocol.Reference)
    (available : Available heap (.node entry stored depth free))
    (members : ∀ edge ∈ selected, edge ∈ stored)
    (lengths : selected.length ≤ stored.length)
    (scs : List Suspended) (start : Nat) (inheritedBound : scs.length ≤ inherited) :
    SourcePruningEnumerationNativeBranchCompletion.cost scs start selected ≤ count seed inherited := by
  have resident (edge : EdgeValue Symbol Constraint) (member : edge ∈ selected) :
      InternedEdgeResidency.EdgeResident heap edge :=
    InternedEdgeResidency.resident_edges heap linked _ available.resident edge (members edge member)
  have rows := SourceCurrentConstrainedCapRequiredResources.node_width bounded available
  have children (edge : EdgeValue Symbol Constraint) (member : edge ∈ selected) :
      edge.children.length ≤ scalar seed.2 :=
    SourceCurrentConstrainedCapRequiredResources.edge_width bounded edge (resident edge member)
  have own (edge : EdgeValue Symbol Constraint) (member : edge ∈ selected)
      (tries : List EqualityTrie.Trie) (residual : Option Constraint)
      (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual)) :
      tries.length ≤ SourcePruningEnumerationGuardWidth.width seed.1 :=
    SourcePruningEnumerationGuardWidth.project_le seed.1 edge.entry.key.constraint tries residual
      (known edge.entry.key edge (resident edge member)) projected
  have exactCost := SourcePruningEnumerationCostBounds.cost_le scs start selected
    (scalar seed.2) (scalar seed.2) (SourcePruningEnumerationGuardWidth.width seed.1)
    (Nat.le_trans lengths rows) children own
  exact Nat.le_trans exactCost (Nat.mul_le_mul_left _ (Nat.add_le_add_right
    (Nat.add_le_add_right inheritedBound _) 1))

end MicroCFTA.SourcePruningEnumerationOriginalForecast
