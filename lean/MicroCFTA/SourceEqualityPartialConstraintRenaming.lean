import MicroCFTA.CacheRenaming
import MicroCFTA.SourceEqualityPartialMemoFrame

/-!
# Physical constraint and result-memo keys across allocation histories

Contradiction keeps its separate tag. Live identities correspond through
their stored ordered trie keys. The production-side table can contain extra
allocations. No equality of numeric counters or issued identities is required.
Actual source allocation events and machine identity capacity remain separate
implementation obligations.
-/
namespace MicroCFTA.SourceEqualityPartialConstraintRenaming
open Cache SourceEqualityPartialConstraintKey SourceEqualityPartialKeyTransport
variable {first second after firstAfter secondAfter : Cache.State SourceEqualityPartialConstraintKey.Key}

/-- Tagged constraint identities correspond through their canonical physical keys. -/
def Linked (first second : Cache.State SourceEqualityPartialConstraintKey.Key) : Option Nat → Option Nat → Prop
  | none, none => True
  | some left, some right => CacheRenaming.Linked first second left right
  | _, _ => False

/-- Every two valid allocation histories preserve tagged identity equality in both directions. -/
theorem linked_eq_iff (firstValid : Cache.Valid first) (secondValid : Cache.Valid second)
    (left : Linked first second a b) (right : Linked first second c d) : a = c ↔ b = d := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp only [Linked] at left right <;> try contradiction
  all_goals try simp
  exact CacheRenaming.linked_eq_iff firstValid secondValid left right

/-- Table growth preserves every tagged constraint identity pair. -/
theorem Linked.grows (linked : Linked first second left right)
    (firstGrowth : Cache.Extends first.table firstAfter.table) (secondGrowth : Cache.Extends second.table secondAfter.table) :
    Linked firstAfter secondAfter left right := by
  cases left <;> cases right <;> simp only [Linked] at linked ⊢ <;> try contradiction
  exact linked.grows firstGrowth secondGrowth

/-- Independent permitted atomic activity retains the physical identity relation. -/
theorem Linked.steps (linked : Linked first second left right)
    (firstSteps : Cache.Steps first firstAfter) (secondSteps : Cache.Steps second secondAfter) :
    Linked firstAfter secondAfter left right :=
  linked.grows (Cache.steps_table_extends firstSteps) (Cache.steps_table_extends secondSteps)

/-- Reconstructed empty tables are covered by every production-side constraint table. -/
theorem empty_covered (source : Cache.State SourceEqualityPartialConstraintKey.Key) :
    CacheRenaming.Covers Cache.emptyState source := by
  intro key entry impossible
  cases impossible

/-- Actual shared payload identification preserves coverage of the reconstructed table. -/
theorem identify_covers (payload : SourceEqualityPrecheck.Constraint)
    (covered : CacheRenaming.Covers first second) (secondValid : Cache.Valid second) :
    CacheRenaming.Covers (identify payload first).2 (identify payload second).2 := by
  cases payload with
  | none => exact covered
  | some records => exact CacheRenaming.covers_intern first second covered secondValid (key records)

/-- Actual payload identification relates its returned identities despite different counters. -/
theorem identify_linked (payload : SourceEqualityPrecheck.Constraint)
    (firstValid : Cache.Valid first) (secondValid : Cache.Valid second) :
    Linked (identify payload first).2 (identify payload second).2 (identify payload first).1 (identify payload second).1 := by
  cases payload with
  | none => trivial
  | some records => exact CacheRenaming.linked_intern first second firstValid secondValid (key records)

/-- Renaming a recorded canonical identity retains the exact original physical payload. -/
theorem recorded_transport (firstValid : Cache.Valid first)
    (payload : SourceEqualityPrecheck.Constraint) (firstId secondId : Option Nat)
    (recorded : Recorded first payload firstId) (linked : Linked first second firstId secondId) :
    Recorded second payload secondId := by
  cases payload with
  | none => cases firstId <;> cases secondId <;> simp_all [Recorded, Linked]
  | some records =>
      cases firstId with
      | none => contradiction
      | some firstId =>
          cases secondId with
          | none => contradiction
          | some secondId =>
              obtain ⟨entry, stored, identity⟩ := recorded
              obtain ⟨shared, leftEntry, rightEntry, leftStored, rightStored, leftIdentity, rightIdentity⟩ := linked
              have same := (Cache.identity_eq_iff_key_eq first firstValid stored leftStored).mp
                (identity.trans leftIdentity.symm)
              exact ⟨rightEntry, same ▸ rightStored, rightIdentity⟩

/-- Recorded related identities determine the same complete tagged physical constraint key. -/
theorem recorded_key_eq (firstValid : Cache.Valid first) (secondValid : Cache.Valid second)
    (firstPayload secondPayload : SourceEqualityPrecheck.Constraint) (firstId secondId : Option Nat)
    (firstRecorded : Recorded first firstPayload firstId) (secondRecorded : Recorded second secondPayload secondId)
    (linked : Linked first second firstId secondId) : firstPayload.map key = secondPayload.map key := by
  cases firstPayload with
  | none =>
      cases firstId <;> cases secondPayload <;> cases secondId <;> simp_all [Recorded, Linked]
  | some firstRecords =>
      cases firstId with
      | none => contradiction
      | some firstId =>
          cases secondPayload with
          | none => cases secondId <;> simp_all [Recorded, Linked]
          | some secondRecords =>
              cases secondId with
              | none => contradiction
              | some secondId =>
                  obtain ⟨firstEntry, firstStored, firstIdentity⟩ := firstRecorded
                  obtain ⟨secondEntry, secondStored, secondIdentity⟩ := secondRecorded
                  obtain ⟨shared, leftEntry, rightEntry, leftStored, rightStored, leftIdentity, rightIdentity⟩ := linked
                  have firstKey := (Cache.identity_eq_iff_key_eq first firstValid firstStored leftStored).mp
                    (firstIdentity.trans leftIdentity.symm)
                  have secondKey := (Cache.identity_eq_iff_key_eq second secondValid secondStored rightStored).mp
                    (secondIdentity.trans rightIdentity.symm)
                  exact congrArg some (firstKey.trans secondKey.symm)

/-- Physical identity renaming preserves satisfaction of actual well-formed inherited payloads. -/
theorem sat (firstValid : Cache.Valid first) (secondValid : Cache.Valid second)
    (firstPayload secondPayload : SourceEqualityPrecheck.Constraint) (firstId secondId : Option Nat)
    (firstRecorded : Recorded first firstPayload firstId) (secondRecorded : Recorded second secondPayload secondId)
    (linked : Linked first second firstId secondId)
    (firstWellFormed : SourceEqualityDescend.WellFormed firstPayload)
    (secondWellFormed : SourceEqualityDescend.WellFormed secondPayload) (term : Language.Term Symbol) :
    SourceEqualityPrecheck.Sat term firstPayload ↔ SourceEqualityPrecheck.Sat term secondPayload :=
  sat_of_key firstPayload secondPayload firstWellFormed secondWellFormed
    (recorded_key_eq firstValid secondValid firstPayload secondPayload firstId secondId firstRecorded secondRecorded linked) term

/-- Result-memo keys relate only the constraint identity and retain the complete node reference. -/
def KeyLinked (first second : Cache.State SourceEqualityPartialConstraintKey.Key)
    (left right : SourceEqualityPartialMemoWorker.Key) : Prop := Linked first second left.1 right.1 ∧ left.2 = right.2

/-- Related complete memo keys preserve hit equality in both directions. -/
theorem key_eq_iff (firstValid : Cache.Valid first) (secondValid : Cache.Valid second)
    (left : KeyLinked first second a b) (right : KeyLinked first second c d) : a = c ↔ b = d := by
  rw [Prod.mk.injEq, Prod.mk.injEq]
  exact and_congr (linked_eq_iff firstValid secondValid left.1 right.1)
    (by rw [left.2, right.2])

/-- Preparing the same actual request in independently allocated full states gives corresponding full keys. -/
theorem prepare_linked (request : SourceEqualityPartialMemoWorker.Request)
    (firstState secondState : SourceEqualityPartialMemoWorker.State width)
    (firstValid : Cache.Valid firstState.constraints) (secondValid : Cache.Valid secondState.constraints) :
    KeyLinked (SourceEqualityPartialMemoWorker.prepare request firstState).2.constraints
      (SourceEqualityPartialMemoWorker.prepare request secondState).2.constraints
      (SourceEqualityPartialMemoWorker.prepare request firstState).1 (SourceEqualityPartialMemoWorker.prepare request secondState).1 :=
  ⟨identify_linked request.inherited firstValid secondValid, rfl⟩

end MicroCFTA.SourceEqualityPartialConstraintRenaming
