import MicroCFTA.SourceCurrentEqualityAbsorption
import MicroCFTA.SourceCurrentNormalizedInheritedPrefix

/-!
# Actual equality operations with covered own classes

Covered own equalities leave a fixed inherited value unchanged. Cold and
warm combination retain the complete physical value and its identity.
The actual field accessor and prefix derive the same result. Nonempty
inherited descent then strictly decreases path height.
-/
namespace MicroCFTA.SourceCurrentAllocatedEqualityAbsorption
open SourceEqualityClassOrder SourceEqualityConstraintAllocation
open SourceCurrentEqualityNormalizationFixed (Fixed)
open EqualityNormalize (Covers)
local notation "Operations" => SourceEqualityConstraintMemoAllocation.State
local notation "Valid" => SourceEqualityConstraintMemoAllocation.Valid
local notation "Grows" => SourceEqualityConstraintMemoAllocation.Grows
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "prefixRun" => SourceCurrentAllocatedInheritedPrefix.run

private theorem stored_eq (state : Operations) (first second : Value)
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
          obtain ⟨firstEntry,firstPresent,firstSame⟩ := firstStored
          obtain ⟨secondEntry,secondPresent,secondSame⟩ := secondStored
          have entries := Option.some.inj (firstPresent.symm.trans secondPresent)
          rw [firstSame.symm.trans (entries ▸ secondSame)]

/-- Actual cold or warm combination retains the complete value when all own classes are covered. -/
theorem combine (identity ownIdentity : Nat) (records ownRecords : List Record)
    (before : Operations) (valid : Valid before)
    (ready : Ready before.constraints (.live identity records))
    (ownReady : Ready before.constraints (.live ownIdentity ownRecords))
    (fixed : Fixed (records.map Record.paths))
    (covered : Covers (ownRecords.map Record.paths) (records.map Record.paths)) :
    (SourceEqualityConstraintMemoAllocation.combine (.live identity records) (.live ownIdentity ownRecords) before).1 =
        .ok (.live identity records) ∧
      Valid (SourceEqualityConstraintMemoAllocation.combine (.live identity records) (.live ownIdentity ownRecords) before).2 ∧
      Ready (SourceEqualityConstraintMemoAllocation.combine (.live identity records) (.live ownIdentity ownRecords) before).2.constraints
        (.live identity records) ∧
      Grows before (SourceEqualityConstraintMemoAllocation.combine (.live identity records) (.live ownIdentity ownRecords) before).2 := by
  obtain ⟨result,done,finalValid,resultReady,payload,growth⟩ :=
    SourceEqualityConstraintMemoAllocation.combine_correct (.live identity records) (.live ownIdentity ownRecords) before
      valid ready ownReady
  have pure : SourceEqualityInheritedPayload.combine (some records) (some ownRecords) = .ok (some records) := by
    change SourceEqualityPhysicalPayload.read (SourceCompactGuards.combineEqualities
      (some (records.map Record.paths)) (some (ownRecords.map Record.paths))) = .ok (some records)
    rw [SourceCurrentEqualityAbsorption.combine _ _ fixed covered]
    exact SourceCurrentEqualityPayloadReadback.read (some records) ready.2
  have exactPayload : result.payload = (.live identity records : Value).payload :=
    Except.ok.inj (payload.symm.trans pure)
  have same := stored_eq _ result (.live identity records) resultReady.1
    (ready.grows growth.constraint_growth).1 exactPayload
  subst result
  exact ⟨done,finalValid,resultReady,growth⟩

/-- An actual covered field accessor and prefix preserve the fixed inherited value and identity. -/
theorem prefix (original : Guard) (identity : Nat) (records : List Record)
    (ownClasses : EqualityNormalize.Constraints) (before : Operations) (valid : Valid before)
    (ready : Ready before.constraints (.live identity records))
    (field : SourceCurrentConjunctionEquality.FieldAvailable before original)
    (compiled : SourceCompactGuards.sourceEqualities original = some ownClasses)
    (fixed : Fixed (records.map Record.paths))
    (covered : Covers ownClasses (records.map Record.paths)) :
    (prefixRun original (.live identity records) before).1 = .ok (some (.live identity records)) ∧
      Valid (prefixRun original (.live identity records) before).2 ∧
      Ready (prefixRun original (.live identity records) before).2.constraints (.live identity records) ∧
      Grows before (prefixRun original (.live identity records) before).2 := by
  obtain ⟨own,loaded,accessorValid,ownReady,classes,_,accessorGrowth⟩ :=
    SourceCurrentConjunctionEquality.accessor_correct original before valid field
  rw [compiled] at classes
  cases own with
  | contradiction => cases classes
  | live ownIdentity ownRecords =>
      have ownSame : ownRecords.map Record.paths = ownClasses := Option.some.inj classes
      have combined := combine identity ownIdentity records ownRecords _ accessorValid
        (ready.grows accessorGrowth.constraint_growth) ownReady fixed (ownSame ▸ covered)
      rw [SourceCurrentAllocatedInheritedPrefix.run_combine original identity records before _ loaded]
      exact ⟨by simp only [combined.1,Except.map],combined.2.1,combined.2.2.1,
        SourceCurrentConjunctionEquality.grows_trans accessorGrowth combined.2.2.2⟩

/-- A covered own prefix followed by actual indexed descent strictly lowers nonempty inherited height. -/
theorem descend (original : Guard) (identity : Nat) (records : List Record)
    (ownClasses : EqualityNormalize.Constraints) (index : Nat)
    (before : Operations) (valid : Valid before)
    (ready : Ready before.constraints (.live identity records))
    (field : SourceCurrentConjunctionEquality.FieldAvailable before original)
    (compiled : SourceCompactGuards.sourceEqualities original = some ownClasses)
    (fixed : Fixed (records.map Record.paths))
    (covered : Covers ownClasses (records.map Record.paths)) (nonempty : records ≠ []) :
    (prefixRun original (.live identity records) before).1 = .ok (some (.live identity records)) ∧
      SourceCurrentOuterInheritedDescent.pathHeight
        (SourceEqualityConstraintMemoAllocation.descend (.live identity records) index
          (prefixRun original (.live identity records) before).2).1 <
        SourceCurrentOuterInheritedDescent.pathHeight (.live identity records) ∧
      (SourceEqualityConstraintMemoAllocation.descend (.live identity records) index
        (prefixRun original (.live identity records) before).2).1.identity ≠ some identity := by
  have actual := prefix original identity records ownClasses before valid ready field compiled fixed covered
  exact ⟨actual.1,SourceCurrentOuterInheritedDescent.descend_lt identity records index _
    actual.2.1 actual.2.2.1 nonempty,
    SourceCurrentOuterInheritedDescent.descend_identity_ne identity records index _
      actual.2.1 actual.2.2.1 nonempty⟩

end MicroCFTA.SourceCurrentAllocatedEqualityAbsorption
