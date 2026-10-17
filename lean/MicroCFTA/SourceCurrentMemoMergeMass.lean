import MicroCFTA.SourceCurrentMemoMergeEffects
import MicroCFTA.SourceCurrentMemoMergeOrigins
import MicroCFTA.InternedValueMassHeap

/-!
# Causal mass of actual merge memo winners

The physical memo invariant makes every stored result available. The
current heap bound then bounds that exact result. Completion reads the
current table after its body. An earlier winner uses its own stored
payload bound, including when the candidate is smaller.

These laws transport proved current invariants. They do not construct a
merge execution or establish a resource bound for its recursive body.
-/
namespace MicroCFTA.SourceCurrentMemoMergeMass
open InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentMemoMergeGraph
variable {Symbol Guard : Type} {bound : Nat}

/-- Every physical memo entry inherits the current heap's payload bound. -/
theorem entry_bound {heap : State Symbol Guard} {memo : Memo Symbol Guard}
    (physical : SourceCurrentMemoMergeEffects.Stored heap memo)
    (stored : InternedValueMassHeap.Stored bound heap)
    {key : InternedBinderProtocol.NodeRef} {entry : Entry Symbol Guard}
    (found : memo key = some entry) :
    InternedValueMass.value entry.original ≤ bound ∧ InternedValueMass.value entry.result ≤ bound := by
  have known := physical key entry found
  exact ⟨InternedValueMassHeap.available heap stored entry.original known.2.1,
    InternedValueMassHeap.available heap stored entry.result known.2.2.1⟩

/-- An actual warm lookup bounds its returned record without running a body. -/
theorem hit_bound {heap : State Symbol Guard} {memo : Memo Symbol Guard}
    (physical : SourceCurrentMemoMergeEffects.Stored heap memo)
    (stored : InternedValueMassHeap.Stored bound heap)
    {input : Value Symbol Guard} {entry : Entry Symbol Guard}
    (found : memo input.referenceOf = some entry) :
    Available heap entry.result ∧ InternedValueMass.value entry.result ≤ bound :=
  ⟨(physical _ entry found).2.2.1, (entry_bound physical stored found).2⟩

/-- Completion bounds the current winner or its actual available candidate. -/
theorem winner_bound {heap : State Symbol Guard} {memo : Memo Symbol Guard}
    (physical : SourceCurrentMemoMergeEffects.Stored heap memo)
    (stored : InternedValueMassHeap.Stored bound heap)
    (input candidate : Value Symbol Guard) (available : Available heap candidate) :
    Available heap (winner memo input candidate).result ∧
      InternedValueMass.value (winner memo input candidate).result ≤ bound := by
  rcases remember_cases memo input candidate input.referenceOf (winner memo input candidate)
      (winner_found memo input candidate) with old | ⟨_, same⟩
  · exact hit_bound physical stored old
  · rw [same]
    exact ⟨available, InternedValueMassHeap.available heap stored candidate available⟩

section
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A supplied actual call returns the exact record bounded by its final memo and heap. -/
theorem call_bound {clear : Guard → Bool} {top : Guard} {input output : Value Symbol Guard}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard}
    (actual : Call clear top input before memo output after saved)
    (physical : SourceCurrentMemoMergeEffects.Stored after saved)
    (stored : InternedValueMassHeap.Stored bound after) :
    Available after output ∧ InternedValueMass.value output ≤ bound := by
  obtain ⟨entry, found, same⟩ := SourceCurrentMemoMergeOrigins.call_returned actual
  exact same ▸ hit_bound physical stored found

end
end MicroCFTA.SourceCurrentMemoMergeMass
