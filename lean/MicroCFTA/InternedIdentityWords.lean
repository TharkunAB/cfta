import MicroCFTA.DecoderMachineBounds
import MicroCFTA.Cache

/-!
# Machine-word identity supply

The source atomically returns the old Int counter and increments it. A draw
ordinal is an unbounded proof counter. Stored identities are signed words.
Freshness holds within one complete word period, not for unlimited draws.
-/
namespace MicroCFTA.InternedIdentityWords
open DecoderMachineBounds

/-- Execute successive fetch-and-add counter updates from the source initial zero. -/
def counter (bits : Nat) : Nat → Nat
  | 0 => 0
  | draws + 1 => add bits (counter bits draws) (cast bits 1)

/-- Every counter state is the draw ordinal reduced to its actual stored word. -/
theorem counter_exact (bits draws : Nat) : counter bits draws = cast bits draws := by
  induction draws with
  | zero => simp [counter, DecoderMachineBounds.cast]
  | succ draws ih => rw [counter, ih, add_cast]

/-- The source returns the signed previous counter as its new identity. -/
def identity (bits ordinal : Nat) : Int := signed bits (counter bits ordinal)

/-- The actual returned identity is the signed narrowing of its draw ordinal. -/
theorem identity_exact (bits ordinal : Nat) : identity bits ordinal = narrow bits ordinal := by
  rw [identity, counter_exact]
  rfl

/-- Signed reads remain injective over the full stored word interval. -/
theorem signed_injective (bits left right : Nat) (leftBound : left < modulus bits)
    (rightBound : right < modulus bits) (same : signed bits left = signed bits right) : left = right := by
  have halfPositive := half_positive bits
  have leftCast : cast bits left = left := Nat.mod_eq_of_lt leftBound
  have rightCast : cast bits right = right := Nat.mod_eq_of_lt rightBound
  simp only [signed, leftCast, rightCast] at same
  unfold modulus at leftBound rightBound same
  split at same <;> split at same <;> omega

/-- Every draw before one full wrap has a distinct identity, including negative signed identities. -/
theorem fresh_within_period (bits first second : Nat)
    (firstBound : first < modulus bits) (secondBound : second < modulus bits)
    (same : identity bits first = identity bits second) : first = second := by
  rw [identity, counter_exact, identity, counter_exact] at same
  have firstCast : cast bits first = first := Nat.mod_eq_of_lt firstBound
  have secondCast : cast bits second = second := Nat.mod_eq_of_lt secondBound
  rw [firstCast, secondCast] at same
  exact signed_injective bits first second firstBound secondBound same

/-- Up to the signed maximum, source identity order is also the allocation order. -/
theorem ordered_before_sign_wrap (bits first second : Nat) (before : first < second)
    (fits : second ≤ maximum bits) : identity bits first < identity bits second := by
  rw [identity_exact, narrow_exact bits first (by omega), identity_exact, narrow_exact bits second fits]
  omega

/-- A full word period repeats the initial identity. The source has no overflow guard. -/
theorem full_wrap (bits : Nat) : identity bits (modulus bits) = identity bits 0 := by
  simp only [identity, counter_exact, DecoderMachineBounds.cast, Nat.mod_self, Nat.zero_mod]

/-- Global injectivity for unlimited allocations is impossible for the actual finite-word supply. -/
theorem not_unconditionally_fresh (bits : Nat) : ¬ Function.Injective (identity bits) := by
  intro injective
  have equal := injective (full_wrap bits)
  have positive := half_positive bits
  unfold modulus at equal
  omega

/-- A finite atomic draw trace has no reused identity while its draw count stays within one period. -/
theorem finite_trace_distinct (bits draws : Nat) (within : draws ≤ modulus bits) :
    (List.ofFn (fun ordinal : Fin draws => identity bits ordinal.val)).Nodup := by
  apply List.nodup_iff_eq_of_getElem_eq.mpr
  intro first second firstBound secondBound same
  simp only [List.getElem_ofFn] at same
  have firstLt : first < draws := by simpa using firstBound
  have secondLt : second < draws := by simpa using secondBound
  exact fresh_within_period bits first second (by omega) (by omega) same

/-- Interleaved callers cannot collide when each receives a distinct valid draw ordinal. -/
theorem interleaved_fresh (bits : Nat) (ordinal : Caller → Nat)
    (different : Function.Injective ordinal) (within : ∀ caller, ordinal caller < modulus bits) :
    Function.Injective (fun caller => identity bits (ordinal caller)) := by
  intro first second same
  exact different (fresh_within_period bits _ _ (within first) (within second) same)

end MicroCFTA.InternedIdentityWords
