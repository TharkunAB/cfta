import MicroCFTA.InternedFlatProbeTrace

/-!
# Derived absence of body references from both stored probes

For the ordinary callback history, each stored free name occurs in an
actual probe. Absence from both probes therefore implies absence from the
Mu. A different name is also absent from the actual stored body.
-/
namespace MicroCFTA.InternedFlatProbeAbsence
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedFlatProbeHeap InternedFlatProbeTrace InternedFreeOccurrenceRank
open InternedBinderProtocol (Reference NodeKey)

/-- Actual stored free names occur in at least one of their original canonical probes. -/
theorem free_in_probes [DecidableEq (EdgeKey Symbol Guard)] {state : State Symbol Guard} (history : History state)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (available : Available state (.mu entry body depth ordinary)) (name : Reference)
    (member : name ∈ (Value.mu entry body depth ordinary).free) :
    name ∈ depth.free ∨ name ∈ ordinary.free := by
  have facts := (history_correct history).1
  have related := stored_related history entry.key (.mu entry body depth ordinary) (available.resident entry rfl)
  obtain ⟨count, occurrence⟩ := (costs_free _ state facts.coherent available name).mpr member
  obtain ⟨prior, _, selected⟩ := related name count occurrence
  rcases selected with left | right
  · left
    apply (costs_free depth state facts.coherent (available.children depth (by simp [InternedProbeProvenance.children])) name).mp
    exact ⟨prior, left⟩
  · right
    apply (costs_free ordinary state facts.coherent (available.children ordinary (by simp [InternedProbeProvenance.children])) name).mp
    exact ⟨prior, right⟩

/-- A name absent from both actual probes is absent from the stored Mu free set. -/
theorem mu_absent [DecidableEq (EdgeKey Symbol Guard)] {state : State Symbol Guard} (history : History state)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (available : Available state (.mu entry body depth ordinary)) (name : Reference)
    (depthAbsent : name ∉ depth.free) (ordinaryAbsent : name ∉ ordinary.free) :
    name ∉ (Value.mu entry body depth ordinary).free := by
  intro member
  exact (free_in_probes history entry body depth ordinary available name member).elim depthAbsent ordinaryAbsent

/-- An external name absent from both probes is absent from the actual stored body as well. -/
theorem body_absent [DecidableEq (EdgeKey Symbol Guard)] {state : State Symbol Guard} (history : History state)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (available : Available state (.mu entry body depth ordinary)) (name : Reference)
    (different : name ≠ .interned entry.identity)
    (depthAbsent : name ∉ depth.free) (ordinaryAbsent : name ∉ ordinary.free) : name ∉ body.free := by
  intro member
  exact mu_absent history entry body depth ordinary available name depthAbsent ordinaryAbsent
    (by simp [Value.free, member, different])

end MicroCFTA.InternedFlatProbeAbsence
