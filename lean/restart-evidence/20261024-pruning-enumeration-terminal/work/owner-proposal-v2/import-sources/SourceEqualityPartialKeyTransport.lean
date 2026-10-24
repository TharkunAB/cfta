import MicroCFTA.SourceEqualityPartialConstraintKey
import MicroCFTA.SourceEqualityDescend
import MicroCFTA.InternedProbeProvenance
import MicroCFTA.InternedGuardedLanguage

/-!
# Immutable meaning transport for equal partial-reduction keys

Coherent class metadata gives the same equality predicate for equal trie
keys. Resident node references determine the complete immutable value.
These facts transport a completed result's narrowing and contextual meaning.
Current heap effects and completed-cell provenance remain separate facts.
-/
namespace MicroCFTA.SourceEqualityPartialKeyTransport
open Cache Language EqualityNormalize SourceEqualityClassOrder
open SourceEqualityPartialConstraintKey InternedConstructorTemplates InternedProbeProvenance

private theorem record_sat (first second : Record) (firstCoherent : Coherent first)
    (secondCoherent : Coherent second) (same : first.trie = second.trie) (term : Term Symbol) :
    ClassSat term first.paths ↔ ClassSat term second.paths := by
  apply classSat_congr
  intro path
  exact (firstCoherent.2.2 path).symm.trans (same ▸ secondCoherent.2.2 path)

private theorem records_sat (first second : List Record)
    (firstCoherent : ∀ record ∈ first, Coherent record) (secondCoherent : ∀ record ∈ second, Coherent record)
    (same : key first = key second) (term : Term Symbol) :
    Satisfies term (first.map Record.paths) ↔ Satisfies term (second.map Record.paths) := by
  induction first generalizing second with
  | nil =>
      cases second with
      | nil => rfl
      | cons _ _ => simp [key] at same
  | cons first rest ih =>
      cases second with
      | nil => simp [key] at same
      | cons second remaining =>
          change first.trie :: key rest = second.trie :: key remaining at same
          have equal := List.cons.inj same
          have heads := record_sat first second (firstCoherent _ List.mem_cons_self)
            (secondCoherent _ List.mem_cons_self) equal.1 term
          have tails := ih remaining (fun record member => firstCoherent record (List.mem_cons_of_mem _ member))
            (fun record member => secondCoherent record (List.mem_cons_of_mem _ member)) equal.2
          simpa only [List.map_cons, satisfies_cons] using and_congr heads tails

/-- Equal tagged physical keys preserve satisfaction of well-formed inherited payloads. -/
theorem sat_of_key (first second : SourceEqualityPrecheck.Constraint)
    (firstWellFormed : SourceEqualityDescend.WellFormed first)
    (secondWellFormed : SourceEqualityDescend.WellFormed second)
    (same : first.map key = second.map key) (term : Term Symbol) :
    SourceEqualityPrecheck.Sat term first ↔ SourceEqualityPrecheck.Sat term second := by
  cases first with
  | none => cases second <;> simp_all [SourceEqualityPrecheck.Sat]
  | some first =>
      cases second with
      | none => simp at same
      | some second =>
          exact records_sat first second (fun record member => (firstWellFormed first rfl record member).1)
            (fun record member => (secondWellFormed second rfl record member).1) (Option.some.inj same) term

/-- A physical payload identity has its actual trie key in the common interner. -/
def Recorded (state : Cache.State Key) (payload : SourceEqualityPrecheck.Constraint) (identity : Option Nat) : Prop :=
  match payload, identity with
  | none, none => True
  | some records, some identity =>
      ∃ entry, state.table (key records) = some entry ∧ entry.identity = identity
  | _, _ => False

/-- Actual payload identification supplies its stored-identity witness. -/
theorem recorded_identify (before : Cache.State Key) (valid : Cache.Valid before)
    (payload : SourceEqualityPrecheck.Constraint) :
    Recorded (identify payload before).2 payload (identify payload before).1 := by
  cases payload with
  | none => trivial
  | some records =>
      exact ⟨(Cache.intern before (key records)).1, (Cache.intern_correct before (key records) valid).2.1, rfl⟩

/-- Stored payload identities survive actual interner table growth. -/
theorem Recorded.grows {before after : Cache.State Key} {payload : SourceEqualityPrecheck.Constraint} {identity : Option Nat}
    (recorded : Recorded before payload identity) (growth : Cache.Extends before.table after.table) :
    Recorded after payload identity := by
  cases payload <;> cases identity <;> simp only [Recorded] at recorded ⊢
  obtain ⟨entry, present, same⟩ := recorded
  exact ⟨entry, growth _ _ present, same⟩

/-- Equal recorded identities in one valid interner determine the tagged physical key. -/
theorem recorded_key_eq (state : Cache.State Key) (valid : Cache.Valid state)
    (first second : SourceEqualityPrecheck.Constraint) (identity : Option Nat)
    (firstRecorded : Recorded state first identity) (secondRecorded : Recorded state second identity) :
    first.map key = second.map key := by
  cases identity with
  | none =>
      cases first <;> cases second <;> simp_all [Recorded]
  | some identity =>
      cases first with
      | none => cases firstRecorded
      | some first =>
          cases second with
          | none => cases secondRecorded
          | some second =>
              obtain ⟨firstEntry, firstPresent, firstIdentity⟩ := firstRecorded
              obtain ⟨secondEntry, secondPresent, secondIdentity⟩ := secondRecorded
              exact congrArg some ((identity_iff state valid firstPresent secondPresent).mp
                (firstIdentity.trans secondIdentity.symm))

/-- Equal recorded identities preserve every well-formed inherited satisfaction predicate. -/
theorem sat_of_identity (state : Cache.State Key) (valid : Cache.Valid state)
    (first second : SourceEqualityPrecheck.Constraint) (identity : Option Nat)
    (firstWellFormed : SourceEqualityDescend.WellFormed first)
    (secondWellFormed : SourceEqualityDescend.WellFormed second)
    (firstRecorded : Recorded state first identity) (secondRecorded : Recorded state second identity)
    (term : Term Symbol) :
    SourceEqualityPrecheck.Sat term first ↔ SourceEqualityPrecheck.Sat term second :=
  sat_of_key first second firstWellFormed secondWellFormed
    (recorded_key_eq state valid first second identity firstRecorded secondRecorded) term

/-- Equal references of available values determine their complete records in one coherent heap. -/
theorem available_reference_eq (heap : InternedConstructorTemplates.State Symbol Guard)
    (coherent : InternedRecordCoherence.Coherent heap) (first second : Value Symbol Guard)
    (firstAvailable : Available heap first) (secondAvailable : Available heap second)
    (same : first.referenceOf = second.referenceOf) : first = second :=
  InternedFreshProbeKeys.resident_reference_injective heap coherent first second
    firstAvailable.resident secondAvailable.resident same

/-- Equal physical request keys transport only the immutable cached semantic conclusion. -/
theorem cached_meaning (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (heap : InternedConstructorTemplates.State Symbol Guard) (coherent : InternedRecordCoherence.Coherent heap)
    (first second : SourceEqualityPrecheck.Constraint) (original candidate result : Value Symbol Guard)
    (firstWellFormed : SourceEqualityDescend.WellFormed first)
    (secondWellFormed : SourceEqualityDescend.WellFormed second)
    (samePayload : first.map key = second.map key)
    (originalAvailable : Available heap original) (candidateAvailable : Available heap candidate)
    (sameValue : original.referenceOf = candidate.referenceOf)
    (cached : ∀ term,
      (InternedGuardedLanguage.meaning holds ambient result term → InternedGuardedLanguage.meaning holds ambient original term) ∧
      (SourceEqualityPrecheck.Sat term first →
        (InternedGuardedLanguage.meaning holds ambient result term ↔ InternedGuardedLanguage.meaning holds ambient original term))) :
    ∀ term,
      (InternedGuardedLanguage.meaning holds ambient result term → InternedGuardedLanguage.meaning holds ambient candidate term) ∧
      (SourceEqualityPrecheck.Sat term second →
        (InternedGuardedLanguage.meaning holds ambient result term ↔ InternedGuardedLanguage.meaning holds ambient candidate term)) := by
  have values := available_reference_eq heap coherent original candidate originalAvailable candidateAvailable sameValue
  subst candidate
  intro term
  exact ⟨(cached term).1, fun satisfied =>
    (cached term).2 ((sat_of_key first second firstWellFormed secondWellFormed samePayload term).mpr satisfied)⟩

/-- A common stored constraint identity and node reference justify immutable completed-result reuse. -/
theorem cached_identity_meaning (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (heap : InternedConstructorTemplates.State Symbol Guard) (coherent : InternedRecordCoherence.Coherent heap)
    (state : Cache.State Key) (valid : Cache.Valid state)
    (first second : SourceEqualityPrecheck.Constraint) (identity : Option Nat) (original candidate result : Value Symbol Guard)
    (firstWellFormed : SourceEqualityDescend.WellFormed first)
    (secondWellFormed : SourceEqualityDescend.WellFormed second)
    (firstRecorded : Recorded state first identity) (secondRecorded : Recorded state second identity)
    (originalAvailable : Available heap original) (candidateAvailable : Available heap candidate)
    (sameValue : original.referenceOf = candidate.referenceOf)
    (cached : ∀ term,
      (InternedGuardedLanguage.meaning holds ambient result term → InternedGuardedLanguage.meaning holds ambient original term) ∧
      (SourceEqualityPrecheck.Sat term first →
        (InternedGuardedLanguage.meaning holds ambient result term ↔ InternedGuardedLanguage.meaning holds ambient original term))) :
    ∀ term,
      (InternedGuardedLanguage.meaning holds ambient result term → InternedGuardedLanguage.meaning holds ambient candidate term) ∧
      (SourceEqualityPrecheck.Sat term second →
        (InternedGuardedLanguage.meaning holds ambient result term ↔ InternedGuardedLanguage.meaning holds ambient candidate term)) :=
  cached_meaning holds ambient heap coherent first second original candidate result firstWellFormed secondWellFormed
    (recorded_key_eq state valid first second identity firstRecorded secondRecorded)
    originalAvailable candidateAvailable sameValue cached

end MicroCFTA.SourceEqualityPartialKeyTransport
