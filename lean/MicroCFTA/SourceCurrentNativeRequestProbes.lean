import MicroCFTA.SourceCurrentNativeRequestWinner
import MicroCFTA.InternedProfileHeap

/-!
# Exact probe payload after an actual Mu request

The selected winner contains the caller's complete canonical probes.
The proof uses availability at the actual returned heap.
-/
namespace MicroCFTA.SourceCurrentNativeRequestProbes
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Outcome request finish)
open InternedNestedFacts (Facts)
open InternedBinderProtocol (Reference)

/-- A successful physical request selects the exact complete requested probe pair. -/
theorem request_probes [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool)
    (depth ordinary : Value Symbol Guard)
    (callback : Reference → State Symbol Guard → Outcome Symbol Guard (Value Symbol Guard))
    (before : State Symbol Guard) (value : Value Symbol Guard) (after : State Symbol Guard)
    (actual : request smart depth ordinary callback before = .done value after)
    (factsAfter : Facts after) (depthAvailable : Available after depth)
    (ordinaryAvailable : Available after ordinary) :
    ∃ entry body, after.nodeRecords (muKey depth ordinary) = some (.mu entry body depth ordinary) ∧
      value = finish smart (.mu entry body depth ordinary) := by
  obtain ⟨winner, present, returned⟩ := SourceCurrentNativeRequestWinner.winner
    smart depth ordinary callback before value after actual
  obtain ⟨entry, body, rfl⟩ := InternedProfileHeap.stored_probes
    depth ordinary winner after factsAfter depthAvailable ordinaryAvailable present
  exact ⟨entry, body, present, returned⟩

end MicroCFTA.SourceCurrentNativeRequestProbes
