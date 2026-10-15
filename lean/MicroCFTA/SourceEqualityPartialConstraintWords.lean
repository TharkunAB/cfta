import MicroCFTA.SourceEqualityPartialConstraintRenaming
import MicroCFTA.InternedIdentityWords

/-!
# Signed source identities for physical constraint memo keys

Proof identities are reservation ordinals. Source identities are signed
machine words. A bound on the complete reservation supply preserves equality
through signed conversion. The bound includes unused losing candidates.
It does not follow from a bound on requests or resident table entries.
-/
namespace MicroCFTA.SourceEqualityPartialConstraintWords
open Cache SourceEqualityPartialKeyTransport SourceEqualityPartialConstraintRenaming
open SourceEqualityPartialMemoFrame
variable {state : Cache.State SourceEqualityPartialConstraintKey.Key}

/-- A recorded live constraint identity was issued before the current supply counter. -/
theorem recorded_bound (valid : Cache.Valid state) (payload : SourceEqualityPrecheck.Constraint)
    (identity : Nat) (recorded : Recorded state payload (some identity)) : identity < state.next := by
  cases payload with
  | none => contradiction
  | some records =>
      obtain ⟨entry, stored, same⟩ := recorded
      have issued := (valid.2 _ _ stored).2
      rw [same] at issued
      exact valid.1 identity _ issued

/-- Signed machine conversion preserves equality of actual recorded tagged identities within one full period. -/
theorem recorded_eq_iff (bits : Nat) (valid : Cache.Valid state)
    (capacity : state.next ≤ DecoderMachineBounds.modulus bits)
    (firstPayload secondPayload : SourceEqualityPrecheck.Constraint) (firstId secondId : Option Nat)
    (firstRecorded : Recorded state firstPayload firstId) (secondRecorded : Recorded state secondPayload secondId) :
    firstId.map (InternedIdentityWords.identity bits) = secondId.map (InternedIdentityWords.identity bits) ↔ firstId = secondId := by
  cases firstId with
  | none => cases secondId <;> simp
  | some firstId =>
      cases secondId with
      | none => simp
      | some secondId =>
          simp only [Option.map_some, Option.some.injEq]
          constructor
          · intro same
            exact InternedIdentityWords.fresh_within_period bits firstId secondId
              (Nat.lt_of_lt_of_le (recorded_bound valid firstPayload firstId firstRecorded) capacity)
              (Nat.lt_of_lt_of_le (recorded_bound valid secondPayload secondId secondRecorded) capacity) same
          · intro same
            exact congrArg (InternedIdentityWords.identity bits) same

/-- The production key keeps contradiction separate and stores signed live identities. -/
def wordKey (bits : Nat) (key : SourceEqualityPartialMemoWorker.Key) : Option Int × InternedBinderProtocol.NodeRef :=
  (key.1.map (InternedIdentityWords.identity bits), key.2)

/-- Full actual request keys preserve both directions of equality under signed identity conversion. -/
theorem word_key_eq_iff (bits : Nat) (valid : Cache.Valid state)
    (capacity : state.next ≤ DecoderMachineBounds.modulus bits)
    (firstRequest secondRequest : SourceEqualityPartialMemoWorker.Request) (firstKey secondKey : SourceEqualityPartialMemoWorker.Key)
    (firstRecorded : KeyOf state firstRequest firstKey) (secondRecorded : KeyOf state secondRequest secondKey) :
    wordKey bits firstKey = wordKey bits secondKey ↔ firstKey = secondKey := by
  change (firstKey.1.map (InternedIdentityWords.identity bits), firstKey.2) =
    (secondKey.1.map (InternedIdentityWords.identity bits), secondKey.2) ↔ firstKey = secondKey
  rw [Prod.mk.injEq, Prod.mk.injEq]
  exact and_congr (recorded_eq_iff bits valid capacity firstRequest.inherited secondRequest.inherited
    firstKey.1 secondKey.1 firstRecorded.1 secondRecorded.1) Iff.rfl

/-- Physical key renaming and signed conversion jointly preserve actual result-memo hit equality. -/
theorem renamed_word_key_eq_iff (bits : Nat)
    (first second : Cache.State SourceEqualityPartialConstraintKey.Key)
    (firstValid : Cache.Valid first) (secondValid : Cache.Valid second)
    (capacity : second.next ≤ DecoderMachineBounds.modulus bits)
    (firstRequest secondRequest : SourceEqualityPartialMemoWorker.Request)
    (a b c d : SourceEqualityPartialMemoWorker.Key)
    (firstPair : KeyLinked first second a b) (secondPair : KeyLinked first second c d)
    (firstRecorded : KeyOf second firstRequest b) (secondRecorded : KeyOf second secondRequest d) :
    a = c ↔ wordKey bits b = wordKey bits d :=
  (key_eq_iff firstValid secondValid firstPair secondPair).trans
    (word_key_eq_iff bits secondValid capacity firstRequest secondRequest b d firstRecorded secondRecorded).symm

end MicroCFTA.SourceEqualityPartialConstraintWords
