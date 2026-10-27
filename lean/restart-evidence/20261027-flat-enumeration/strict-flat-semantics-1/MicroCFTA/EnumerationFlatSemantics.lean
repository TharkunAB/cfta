import MicroCFTA.EnumerationFlatAssimilation
import MicroCFTA.FlatUnionFindSemantics

/-!
# Complete assignments for the flat enumeration core

The state relation transports forest equalities, all stored slot restrictions
and all residual guards. It also transports root tests and canonical tries.
It does not assert a bound on the addresses explicitly stored in either map.
-/

namespace MicroCFTA.EnumerationFlatState

open Language Fragments

variable {Symbol Guard : Type} {flat : State Symbol Guard}
  {earlier : EnumerationState.State Symbol Guard}

/-- A complete assignment satisfies forest equalities, stored slots and residual guards. -/
def Satisfies (language : EnumerationCorrectness.NodeLanguage Symbol)
    (meaning : Guard → Term Symbol → Prop) (assignment : Nat → Term Symbol)
    (state : State Symbol Guard) : Prop :=
  (FlatUnionFind.Satisfies state.representatives assignment ∧
    heapSatisfies (EnumerationCorrectness.heap language state.values) assignment) ∧
      EnumerationCorrectness.guardsHold meaning assignment state.obligations

/-- Related complete cores permit exactly the same full assignments. -/
theorem related_satisfies (related : Related flat earlier)
    (language : EnumerationCorrectness.NodeLanguage Symbol)
    (meaning : Guard → Term Symbol → Prop) (assignment : Nat → Term Symbol) :
    EnumerationCorrectness.Satisfies language meaning assignment earlier ↔
      Satisfies language meaning assignment flat := by
  simp only [EnumerationCorrectness.Satisfies, Fragments.stateSatisfies, Satisfies,
    FlatUnionFind.represents_satisfies related.representatives, related.values, related.obligations]

/-- Earlier finite root paths agree exactly with the current direct root test. -/
theorem related_isRoot (related : Related flat earlier) (uv : Nat) :
    EnumerationSchedule.IsRoot earlier.representatives uv ↔
      FlatUnionFind.root flat.representatives uv = uv := by
  constructor
  · rintro ⟨size, path⟩
    exact (UnionFind.reaches_unique (related.representatives uv) path).1
  · intro fixed
    have path := related.representatives uv
    rw [fixed] at path
    exact ⟨_, path⟩

/-- The allocator and slot-array alignment transfers through exact core fields. -/
theorem related_supplyAligned (related : Related flat earlier) :
    EnumerationCorrectness.SupplyAligned earlier ↔ flat.counter = flat.values.length := by
  simp only [EnumerationCorrectness.SupplyAligned, related.counter, related.values]

/-- Canonical suspended tries transfer through the exact stored value array. -/
theorem related_canonical (related : Related flat earlier) :
    EnumerationValidity.Canonical earlier ↔
      ∀ value ∈ flat.values, EnumerationSemantics.ValidSuspended (EnumerationState.references value) := by
  simp only [EnumerationValidity.Canonical, related.values]

/-- Current union adds one value equality and retains every slot and guard restriction. -/
theorem union_satisfies (valid : FlatUnionFind.Valid state.representatives)
    (language : EnumerationCorrectness.NodeLanguage Symbol)
    (meaning : Guard → Term Symbol → Prop) (assignment : Nat → Term Symbol) (left right : Nat) :
    Satisfies language meaning assignment
      {state with representatives := FlatUnionFind.union state.representatives left right} ↔
      Satisfies language meaning assignment state ∧ assignment left = assignment right := by
  simp only [Satisfies, FlatUnionFind.union_satisfies valid]
  constructor
  · rintro ⟨⟨⟨forest, equality⟩, slots⟩, guards⟩
    exact ⟨⟨⟨forest, slots⟩, guards⟩, equality⟩
  · rintro ⟨⟨⟨forest, slots⟩, guards⟩, equality⟩
    exact ⟨⟨⟨forest, equality⟩, slots⟩, guards⟩

end MicroCFTA.EnumerationFlatState
