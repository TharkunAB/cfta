import MicroCFTA.SourceCurrentEqualityPayloadReadback
import MicroCFTA.SourceCurrentEqualityNormalizationFixed
import MicroCFTA.SourceCurrentOuterInheritedDescent

/-!
# Actual plain prefix before strict inherited descent

An initially normalized inherited payload survives combination with an
empty own field. The actual accessor and combination retain the complete
inherited value. Indexed descent then changes its physical request key.
This result does not compare every active ancestor or prove outer completion.
-/
namespace MicroCFTA.SourceCurrentNormalizedInheritedPrefix
open SourceEqualityClassOrder SourceEqualityConstraintAllocation
local notation "Operations" => SourceEqualityConstraintMemoAllocation.State
local notation "Valid" => SourceEqualityConstraintMemoAllocation.Valid
local notation "Grows" => SourceEqualityConstraintMemoAllocation.Grows
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "prefix" => SourceCurrentAllocatedInheritedPrefix.run

private theorem stored_eq_of_payload (state : Operations) (first second : Value)
    (firstStored : Stored state.constraints first) (secondStored : Stored state.constraints second)
    (same : first.payload = second.payload) : first = second := by
  cases first with
  | contradiction => cases second <;> simp_all [Value.payload]
  | live firstIdentity firstRecords =>
      cases second with
      | contradiction => cases same
      | live secondIdentity secondRecords =>
          have records := Option.some.inj same
          subst secondRecords
          obtain ⟨firstEntry, firstPresent, firstSame⟩ := firstStored
          obtain ⟨secondEntry, secondPresent, secondSame⟩ := secondStored
          have entries := Option.some.inj (firstPresent.symm.trans secondPresent)
          have identities := firstSame.symm.trans (entries ▸ secondSame)
          rw [identities]

private theorem pure_empty_right (records : List Record)
    (wellFormed : SourceEqualityDescend.WellFormed (some records))
    (fixed : SourceCompactGuards.normalize (records.map Record.paths) = some (records.map Record.paths)) :
    SourceEqualityInheritedPayload.combine (some records) (some []) = .ok (some records) := by
  change SourceEqualityPhysicalPayload.read
    (SourceCompactGuards.combineEqualities (some (records.map Record.paths)) (some [])) = .ok (some records)
  rw [SourceCurrentEqualityNormalizationFixed.combine_empty_right _ fixed]
  exact SourceCurrentEqualityPayloadReadback.read (some records) wellFormed

/-- Actual empty-own combination retains an initially normalized complete inherited value. -/
theorem combine_empty_right (identity : Nat) (records : List Record) (emptyIdentity : Nat)
    (before : Operations) (valid : Valid before)
    (ready : Ready before.constraints (.live identity records))
    (emptyReady : Ready before.constraints (.live emptyIdentity []))
    (fixed : SourceCompactGuards.normalize (records.map Record.paths) = some (records.map Record.paths)) :
    (SourceEqualityConstraintMemoAllocation.combine (.live identity records) (.live emptyIdentity []) before).1 =
        .ok (.live identity records) ∧
      Valid (SourceEqualityConstraintMemoAllocation.combine (.live identity records) (.live emptyIdentity []) before).2 ∧
      Ready (SourceEqualityConstraintMemoAllocation.combine (.live identity records) (.live emptyIdentity []) before).2.constraints
        (.live identity records) ∧
      Grows before (SourceEqualityConstraintMemoAllocation.combine (.live identity records) (.live emptyIdentity []) before).2 := by
  obtain ⟨result, done, finalValid, resultReady, payload, growth⟩ :=
    SourceEqualityConstraintMemoAllocation.combine_correct (.live identity records) (.live emptyIdentity []) before
      valid ready emptyReady
  have exactPayload : result.payload = (.live identity records : Value).payload :=
    Except.ok.inj (payload.symm.trans (pure_empty_right records ready.2 fixed))
  have same := stored_eq_of_payload _ result (.live identity records) resultReady.1
    (ready.grows growth.constraint_growth).1 exactPayload
  subst result
  exact ⟨done, finalValid, resultReady, growth⟩

/-- An actual available empty-own accessor and inherited prefix retain the normalized inherited value. -/
theorem plain (original : Guard) (identity : Nat) (records : List Record)
    (before : Operations) (valid : Valid before)
    (ready : Ready before.constraints (.live identity records))
    (field : SourceCurrentConjunctionEquality.FieldAvailable before original)
    (emptyOwn : SourceCompactGuards.sourceEqualities original = some [])
    (fixed : SourceCompactGuards.normalize (records.map Record.paths) = some (records.map Record.paths)) :
    (prefix original (.live identity records) before).1 = .ok (some (.live identity records)) ∧
      Valid (prefix original (.live identity records) before).2 ∧
      Ready (prefix original (.live identity records) before).2.constraints (.live identity records) ∧
      Grows before (prefix original (.live identity records) before).2 := by
  obtain ⟨own, loaded, accessorValid, ownReady, classes, _, accessorGrowth⟩ :=
    SourceCurrentConjunctionEquality.accessor_correct original before valid field
  rw [emptyOwn] at classes
  cases own with
  | contradiction => cases classes
  | live emptyIdentity ownRecords =>
      have emptyRecords : ownRecords = [] := by
        have emptyPaths := Option.some.inj classes
        exact List.map_eq_nil_iff.mp emptyPaths
      subst ownRecords
      have combined := combine_empty_right identity records emptyIdentity _ accessorValid
        (ready.grows accessorGrowth.constraint_growth) ownReady fixed
      rw [SourceCurrentAllocatedInheritedPrefix.run_combine original identity records before _ loaded]
      exact ⟨by simp only [combined.1, Except.map], combined.2.1, combined.2.2.1,
        SourceCurrentConjunctionEquality.grows_trans accessorGrowth combined.2.2.2⟩

/-- The actual plain prefix and indexed descent strictly lower nonempty inherited path height. -/
theorem descend (original : Guard) (identity : Nat) (records : List Record) (index : Nat)
    (before : Operations) (valid : Valid before)
    (ready : Ready before.constraints (.live identity records))
    (field : SourceCurrentConjunctionEquality.FieldAvailable before original)
    (emptyOwn : SourceCompactGuards.sourceEqualities original = some [])
    (fixed : SourceCompactGuards.normalize (records.map Record.paths) = some (records.map Record.paths))
    (nonempty : records ≠ []) :
    (prefix original (.live identity records) before).1 = .ok (some (.live identity records)) ∧
      SourceCurrentOuterInheritedDescent.pathHeight
        (SourceEqualityConstraintMemoAllocation.descend (.live identity records) index
          (prefix original (.live identity records) before).2).1 <
        SourceCurrentOuterInheritedDescent.pathHeight (.live identity records) ∧
      (SourceEqualityConstraintMemoAllocation.descend (.live identity records) index
        (prefix original (.live identity records) before).2).1.identity ≠ some identity := by
  have actual := plain original identity records before valid ready field emptyOwn fixed
  exact ⟨actual.1, SourceCurrentOuterInheritedDescent.descend_lt identity records index _
    actual.2.1 actual.2.2.1 nonempty,
    SourceCurrentOuterInheritedDescent.descend_identity_ne identity records index _
      actual.2.1 actual.2.2.1 nonempty⟩

/-- Initial raw classes construct the fixed payload needed by the actual plain prefix and descent. -/
theorem normalized (original : Guard) (classes : EqualityNormalize.Constraints)
    (before : Operations) (valid : Valid before)
    (field : SourceCurrentConjunctionEquality.FieldAvailable before original)
    (emptyOwn : SourceCompactGuards.sourceEqualities original = some []) :
    ∃ inherited cache,
      SourceEqualityConstraintAllocation.normalize classes before.constraints = (.ok inherited, cache) ∧
      let after : Operations := { before with constraints := cache }
      Valid after ∧ Ready cache inherited ∧ Grows before after ∧
      ∀ identity records, inherited = .live identity records → records ≠ [] → ∀ index,
        (prefix original (.live identity records) after).1 = .ok (some (.live identity records)) ∧
        SourceCurrentOuterInheritedDescent.pathHeight
          (SourceEqualityConstraintMemoAllocation.descend (.live identity records) index
            (prefix original (.live identity records) after).2).1 <
          SourceCurrentOuterInheritedDescent.pathHeight (.live identity records) ∧
        (SourceEqualityConstraintMemoAllocation.descend (.live identity records) index
          (prefix original (.live identity records) after).2).1.identity ≠ some identity := by
  obtain ⟨inherited, cache, actual, _, inheritedReady, steps, payloadClasses⟩ :=
    SourceEqualityConstraintAllocation.normalize_complete classes before.constraints valid.constraints
  let after : Operations := { before with constraints := cache }
  have afterValid : Valid after := valid.steps cache steps
  have growth : Grows before after := ⟨steps, Cache.extends_refl _, Cache.extends_refl _⟩
  refine ⟨inherited, cache, actual, afterValid, inheritedReady, growth, ?_⟩
  intro identity records same nonempty index
  have normalized : SourceCompactGuards.normalize classes = some (records.map Record.paths) := by
    simpa only [same, Value.payload, SourceEqualityInheritedPayload.classes, Option.map_some]
      using payloadClasses.symm
  have fixed := SourceCurrentEqualityNormalizationFixed.normalize_idempotent classes _ normalized
  exact descend original identity records index after afterValid (same ▸ inheritedReady)
    (field.grows growth) emptyOwn fixed nonempty

end MicroCFTA.SourceCurrentNormalizedInheritedPrefix
