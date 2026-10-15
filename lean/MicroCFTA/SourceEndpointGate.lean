import MicroCFTA.EndpointRecursionGate
import MicroCFTA.SourceEndpointReachability
import MicroCFTA.InternedFreshOrdinaryGateRank

/-!
# Current endpoint checks on certified source records

The adapter retains actual metadata, original ordered children, and repaired
unfolding with its returned constructor cache. The descendant predicate reads
complete stored records. It does not model the new global predicate memo.
-/
namespace MicroCFTA.SourceEndpointGate
open InternedConstructorTemplates
open InternedFreshOrdinaryGateRank (Node)

/-- Add the current descendant read to the existing certified physical adapter. -/
def read [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool) :
    EndpointRecursionGate.Read (Node Symbol Guard) where
  previous := InternedFreshOrdinaryGateRank.read unconstrained
  reaches node := SourceEndpointReachability.reaches unconstrained node.value

/-- The helper's depth shortcut supplies the endpoint policy's metadata condition. -/
theorem zero_clear [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (node : Node Symbol Guard) (zero : (read unconstrained).nested node = 0) :
    (read unconstrained).reaches node = false :=
  SourceEndpointReachability.zero_clear unconstrained node.value zero

/-- The current ordinary endpoint result is exactly the physical source expression. -/
theorem endpoint [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (node : Node Symbol Guard) (edges : List (List (Node Symbol Guard)))
    (view : InternedFreshOrdinaryGateRank.view node = .branches edges) (fuel : Nat) :
    EndpointRecursionGate.nodeMeets (read unconstrained) (fuel + 1) [] node =
      some (!node.value.free.isEmpty || SourceEndpointReachability.reaches unconstrained node.value) := by
  simpa only [read, InternedFreshOrdinaryGateRank.read_free_empty] using
    EndpointRecursionGate.endpoint (read unconstrained) fuel node edges view (zero_clear unconstrained node)

/-- A concrete constrained-Mu witness below an ordinary endpoint blocks its path. -/
theorem witness_blocks [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (node : Node Symbol Guard) (edges : List (List (Node Symbol Guard)))
    (view : InternedFreshOrdinaryGateRank.view node = .branches edges)
    (witness : SourceEndpointReachability.Witness unconstrained node.value) (fuel : Nat) :
    EndpointRecursionGate.nodeMeets (read unconstrained) (fuel + 1) [] node = some true := by
  rw [endpoint unconstrained node edges view fuel, (SourceEndpointReachability.reaches_iff _ _).mpr witness]
  simp

/-- The changed case has a clear historical result and a blocked current result. -/
theorem closed_witness_changes [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (node : Node Symbol Guard)
    (edges : List (List (Node Symbol Guard)))
    (view : InternedFreshOrdinaryGateRank.view node = .branches edges)
    (closed : node.value.free = []) (witness : SourceEndpointReachability.Witness unconstrained node.value)
    (fuel : Nat) :
    ConstrainedRecursionGate.nodeMeets (InternedFreshOrdinaryGateRank.read unconstrained) (fuel + 1) [] node = some false ∧
    EndpointRecursionGate.nodeMeets (read unconstrained) (fuel + 1) [] node = some true := by
  refine ⟨?_, witness_blocks unconstrained node edges view witness fuel⟩
  simpa only [InternedFreshOrdinaryGateRank.read_free_empty, closed, List.isEmpty_nil, Bool.not_true] using
    ConstrainedRecursionGate.endpoint (InternedFreshOrdinaryGateRank.read unconstrained) fuel node edges view

/-- The new policy retains the actual rank for same-path open-Mu unfolding. -/
def ranking [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool) :
    ConstrainedRecursionGate.UnfoldingRank (read unconstrained).previous :=
  InternedFreshOrdinaryGateRank.ranking unconstrained

end MicroCFTA.SourceEndpointGate
