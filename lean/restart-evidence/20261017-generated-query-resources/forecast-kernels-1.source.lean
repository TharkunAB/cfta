import MicroCFTA.SourceCurrentAllocatedNativeResourceForecast

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option pp.fullNames true

namespace ForecastIntegration
open MicroCFTA.SourceCurrentAllocatedNativeResourceForecast

/-- Every finite forecast has a finite numeric layout reservation. -/
theorem finite_layout (original : Profile) (count : Nat) :
    ∃ bits, Reserved bits original (count + 1) ∧ Room bits original := by
  let last := advance original count
  let bits := last.nodes + last.edges + last.domains +
    2 ^ (last.nodes + last.nodes * last.nodes)
  have self : bits < 2 ^ bits := Nat.lt_two_pow_self
  have nodes : last.nodes ≤ bits := by dsimp [bits]; omega
  have edges : last.edges ≤ bits := by dsimp [bits]; omega
  have domains : last.domains + 2 ^ (last.nodes + last.nodes * last.nodes) ≤ bits := by
    dsimp [bits]
    omega
  have largerEdges : 2 ^ bits ≤ 2 ^ (bits + 2) :=
    Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega)
  have largerDomains : 2 ^ bits ≤ 2 ^ (bits + 1) :=
    Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega)
  have room : Room bits last := ⟨Nat.lt_of_le_of_lt nodes self,
    Nat.le_trans edges (Nat.le_trans (Nat.le_of_lt self) largerEdges),
    Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt domains self) largerDomains⟩
  have reservation := (reserved_iff_last bits original count).mpr room
  exact ⟨bits, reservation, reservation.head⟩

/-- One initial numeric test admits three successive smaller returned profiles. -/
theorem three_queries (bits : Nat) (original firstResult secondResult : Profile)
    (initial : Room bits (advance original 2))
    (firstBound : Le firstResult (step original))
    (secondBound : Le secondResult (step firstResult)) :
    Room bits original ∧ Room bits firstResult ∧ Room bits secondResult ∧
      Reserved bits secondResult 1 ∧ Le (step secondResult) (advance original 3) := by
  have originalReserved : Reserved bits original 3 :=
    (reserved_iff_last bits original 2).mpr initial
  have firstReserved : Reserved bits firstResult 2 := originalReserved.tail.mono firstBound
  have secondReserved : Reserved bits secondResult 1 := firstReserved.tail.mono secondBound
  have finalBound : Le (step secondResult) (advance original 3) :=
    (step_mono secondBound).trans (step_mono (step_mono firstBound))
  exact ⟨originalReserved.head, firstReserved.head, secondReserved.head, secondReserved, finalBound⟩

/-- A reservation splits at any fixed query count without a new room assumption. -/
theorem split_sequence (bits : Nat) (original : Profile) (first last : Nat)
    (reservation : Reserved bits original (first + last)) :
    Reserved bits original first ∧ Reserved bits (advance original first) last := by
  refine ⟨reservation.prefix (by omega), ?_⟩
  intro index less
  rw [← advance_add]
  exact reservation (first + index) (by omega)

end ForecastIntegration

#print axioms ForecastIntegration.finite_layout
#check @ForecastIntegration.finite_layout

#print axioms ForecastIntegration.three_queries
#check @ForecastIntegration.three_queries

#print axioms ForecastIntegration.split_sequence
#check @ForecastIntegration.split_sequence
