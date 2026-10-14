import MicroCFTA.SourceRecursiveIntersectionRowReplay
import MicroCFTA.SourceRecursiveIntersectionReplay

/-!
# Exact surviving product rows of actual ordinary source calls

The actual ordered edge walk replays in the parent's final cache. Canonical
node readback keeps exactly its live returned rows. Each retained row thus
has a matching source pair and an actual allocation-free final-cache call.
-/
namespace MicroCFTA.SourceRecursiveIntersectionKernel
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open EqualityLeafProjectionPhysical (dead normalized_member)

/-- A completed ordinary parent retains resident ordered rows and exact pointwise replay in its final cache. -/
theorem node_rows_replay [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (replay : Replays call) (domain : Interned DomainKey) (left right : List (EdgeValue Symbol Guard))
    (state : Machine Symbol Guard) (valid : Valid state) (known : Domain state domain)
    (leftResident : ∀ edge ∈ left, EdgeResident state.heap edge) (rightResident : ∀ edge ∈ right, EdgeResident state.heap edge)
    (value : Value Symbol Guard) (final : Machine Symbol Guard)
    (done : node emptyGuard conjoin (call domain) left right state = .done value final) :
    ∃ rows, (∀ row ∈ rows, EdgeResident final.heap row) ∧
      All₂ (fun pair row => edge emptyGuard conjoin (call domain) pair.1 pair.2 final = .done row final) (pairs left right) rows ∧
      nodeEdges value = canonicalEdges (surviving rows) := by
  obtain ⟨rows, after, trace, built, exactRows⟩ :=
    node_readback emptyGuard conjoin call calls domain left right state valid known leftResident rightResident value final done
  have walked := (walk_done_iff _ _ _ _ _).mpr trace
  have checked := rows_checked emptyGuard conjoin call calls domain left right state valid known leftResident rightResident
  have afterValid : Valid after := by simpa only [walked, Result.state] using checked.valid
  have resident := checked.result rows after walked
  have builtChecked := work_checked after afterValid (makeNode rows) Available
    (InternedNestedFacts.node_verified rows after.heap afterValid.1 resident)
  have growth : Extension after final := by simpa only [built, Result.state] using builtChecked.extension
  have related := rows_pointwise_replay emptyGuard conjoin call calls replay domain left right state final rows after
    valid known leftResident rightResident walked growth
  exact ⟨rows, (fun row member => edge_grows _ _ growth.heap row (resident row member)), related, exactRows⟩

/-- A completed ordinary node keeps exactly the live rows returned by matched source pairs in its final cache. -/
theorem node_members_replay [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (replay : Replays call) (domain : Interned DomainKey) (left right : List (EdgeValue Symbol Guard))
    (state : Machine Symbol Guard) (valid : Valid state) (known : Domain state domain)
    (leftResident : ∀ edge ∈ left, EdgeResident state.heap edge) (rightResident : ∀ edge ∈ right, EdgeResident state.heap edge)
    (value : Value Symbol Guard) (final : Machine Symbol Guard)
    (done : node emptyGuard conjoin (call domain) left right state = .done value final) (row : EdgeValue Symbol Guard) :
    row ∈ nodeEdges value ↔ ∃ first ∈ left, ∃ second ∈ right,
      first.entry.key.symbol = second.entry.key.symbol ∧
      edge emptyGuard conjoin (call domain) first second final = .done row final ∧ dead row = false := by
  obtain ⟨rows, resident, related, exactRows⟩ :=
    node_rows_replay emptyGuard conjoin call calls replay domain left right state valid known leftResident rightResident value final done
  have checked := node_checked emptyGuard conjoin call calls domain left right state valid known leftResident rightResident
  have finalValid : Valid final := by simpa only [done, Result.state] using checked.valid
  rw [exactRows, normalized_member final.heap finalValid.1.coherent rows resident row,
    pointwise_result_member (fun pair => edge emptyGuard conjoin (call domain) pair.1 pair.2 final) (pairs left right) rows final related row]
  constructor
  · rintro ⟨⟨pair, member, returned⟩, live⟩
    have selected := (pairs_member left right pair).mp member
    exact ⟨pair.1, selected.1, pair.2, selected.2.1, selected.2.2, returned, live⟩
  · rintro ⟨first, firstIn, second, secondIn, label, returned, live⟩
    exact ⟨⟨(first, second), (pairs_member left right (first, second)).mpr ⟨firstIn, secondIn, label⟩, returned⟩, live⟩

/-- The actual full guarded recursive kernel supplies every child correctness and replay premise for ordinary row membership. -/
theorem execute_node_members [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat) (domain : Interned DomainKey)
    (left right : List (EdgeValue Symbol Guard)) (state : Machine Symbol Guard) (valid : Valid state) (known : Domain state domain)
    (leftResident : ∀ edge ∈ left, EdgeResident state.heap edge) (rightResident : ∀ edge ∈ right, EdgeResident state.heap edge)
    (value : Value Symbol Guard) (final : Machine Symbol Guard)
    (done : node emptyGuard conjoin (execute emptyGuard conjoin fuel domain) left right state = .done value final)
    (row : EdgeValue Symbol Guard) :
    row ∈ nodeEdges value ↔ ∃ first ∈ left, ∃ second ∈ right,
      first.entry.key.symbol = second.entry.key.symbol ∧
      edge emptyGuard conjoin (execute emptyGuard conjoin fuel domain) first second final = .done row final ∧ dead row = false :=
  node_members_replay emptyGuard conjoin _ (execute_checked emptyGuard conjoin fuel) (execute_replay emptyGuard conjoin fuel)
    domain left right state valid known leftResident rightResident value final done row

end MicroCFTA.SourceRecursiveIntersectionKernel
