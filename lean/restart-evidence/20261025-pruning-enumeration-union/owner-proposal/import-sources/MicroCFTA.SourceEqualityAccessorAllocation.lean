import MicroCFTA.SourceEqualityGuardAllocation

/-!
# Allocation receipts for the source equality accessor

The accessor retains stored equalities when positive extraction fails or
returns live empty. Other positive payloads use the completed combination
cache. Literal physical readback uses an original constructor receipt.
-/
namespace MicroCFTA.SourceEqualityAccessorAllocation
open SourceEqualityConstraintAllocation
open SourceEqualityConstraintMemoAllocation (State Valid Grows)

/-- Reconstruct the complete source constraint read by this accessor. -/
def constraint (stored : Value) (guard : SourceGuards.Guard Formula) : SourceSymbolicIndex.Constraint Formula :=
  ⟨SourceEqualityInheritedPayload.classes stored.payload, guard⟩

/-- Demand positive equalities and retain the source accessor's two stored-value shortcuts. -/
noncomputable def equalities (stored : Value) (guard : SourceGuards.Guard Formula) (before : State) :
    Except String Value × State :=
  let positive := SourceEqualityGuardAllocation.demandPositive guard before
  match positive.1 with
  | .error message => (.error message, positive.2)
  | .ok none | .ok (some (.live _ [])) => (.ok stored, positive.2)
  | .ok (some added) => SourceEqualityConstraintMemoAllocation.combine stored added positive.2

/-- Pure positive-syntax failure returns the original stored value without allocation. -/
theorem equalities_none (stored : Value) (guard : SourceGuards.Guard Formula) (before : State)
    (failed : SourceEqualityGuardAllocationPlan.make guard = none) :
    equalities stored guard before = (.ok stored, before) := by
  simp only [equalities, SourceEqualityGuardAllocation.demandPositive_none guard before failed]

private theorem grows_trans {before middle after : State} (first : Grows before middle) (second : Grows middle after) :
    Grows before after :=
  ⟨steps_trans first.constraints second.constraints, Cache.extends_trans first.combinations second.combinations,
    Cache.extends_trans first.descents second.descents⟩

/-- A successful normalized constructor receipt derives literal physical reconstruction. -/
theorem read_roundtrip (original : Option EqualityNormalize.Constraints)
    (cached : SourceEqualityGuardReadback.Cached original) (payload : SourceEqualityPrecheck.Constraint)
    (built : SourceEqualityPhysicalPayload.read original = .ok payload) :
    SourceEqualityPhysicalPayload.read (SourceEqualityInheritedPayload.classes payload) = .ok payload := by
  rw [read_classes original cached payload built]
  exact built

private theorem combine_classes (first second result : Value)
    (done : SourceEqualityInheritedPayload.combine first.payload second.payload = .ok result.payload) :
    SourceEqualityInheritedPayload.classes result.payload = SourceCompactGuards.combineEqualities
      (SourceEqualityInheritedPayload.classes first.payload) (SourceEqualityInheritedPayload.classes second.payload) :=
  read_classes _ (SourceEqualityGuardReadback.combine_cached _ _) result.payload done

private theorem combine_roundtrip (first second result : Value)
    (done : SourceEqualityInheritedPayload.combine first.payload second.payload = .ok result.payload) :
    SourceEqualityPhysicalPayload.read (SourceEqualityInheritedPayload.classes result.payload) = .ok result.payload :=
  read_roundtrip _ (SourceEqualityGuardReadback.combine_cached _ _) result.payload done

private theorem equalities_full (stored : Value) (guard : SourceGuards.Guard Formula) (before : State)
    (valid : Valid before) (storedReady : Ready before.constraints stored) :
    ∃ result, (equalities stored guard before).1 = .ok result ∧ Valid (equalities stored guard before).2 ∧
      Ready (equalities stored guard before).2.constraints result ∧
      SourceEqualityInheritedPayload.classes result.payload = SourceCompactGuards.sourceEqualities (constraint stored guard) ∧
      Grows before (equalities stored guard before).2 ∧
      (SourceEqualityPhysicalPayload.read (SourceEqualityInheritedPayload.classes stored.payload) = .ok stored.payload →
        SourceEqualityPhysicalPayload.read (SourceEqualityInheritedPayload.classes result.payload) = .ok result.payload) := by
  obtain ⟨positive, positiveDone, positiveValid, positiveReady, positiveClasses, positiveGrows⟩ :=
    SourceEqualityGuardAllocation.positive_correct guard before valid
  have currentStored := storedReady.grows positiveGrows.constraint_growth
  cases positive with
  | none =>
      have actual : equalities stored guard before = (.ok stored,
          (SourceEqualityGuardAllocation.demandPositive guard before).2) := by
        simp only [equalities, positiveDone]
      rw [actual]
      refine ⟨stored, rfl, positiveValid, currentStored, ?_, positiveGrows, id⟩
      simp only [SourceCompactGuards.sourceEqualities, constraint, ← positiveClasses, Option.map_none]
  | some added =>
      cases added with
      | contradiction =>
          have actual : equalities stored guard before = SourceEqualityConstraintMemoAllocation.combine stored .contradiction
              (SourceEqualityGuardAllocation.demandPositive guard before).2 := by
            simp only [equalities, positiveDone]
          obtain ⟨result, done, afterValid, resultReady, payload, grows⟩ :=
            SourceEqualityConstraintMemoAllocation.combine_correct stored .contradiction _ positiveValid
              currentStored (positiveReady _ rfl)
          rw [actual]
          refine ⟨result, done, afterValid, resultReady, ?_, grows_trans positiveGrows grows,
            fun _ => combine_roundtrip _ _ _ payload⟩
          rw [combine_classes _ _ _ payload]
          simp only [SourceCompactGuards.sourceEqualities, constraint, ← positiveClasses, Option.map_some,
            SourceEqualityInheritedPayload.classes, Value.payload, Option.map_none, SourceCompactGuards.combineEqualities]
      | live identity records =>
          cases records with
          | nil =>
              have actual : equalities stored guard before = (.ok stored,
                  (SourceEqualityGuardAllocation.demandPositive guard before).2) := by
                simp only [equalities, positiveDone]
              rw [actual]
              refine ⟨stored, rfl, positiveValid, currentStored, ?_, positiveGrows, id⟩
              simp only [SourceCompactGuards.sourceEqualities, constraint, ← positiveClasses, Option.map_some,
                SourceEqualityInheritedPayload.classes, Value.payload, List.map_nil]
          | cons head tail =>
              have actual : equalities stored guard before = SourceEqualityConstraintMemoAllocation.combine stored (.live identity (head :: tail))
                  (SourceEqualityGuardAllocation.demandPositive guard before).2 := by
                simp only [equalities, positiveDone]
              obtain ⟨result, done, afterValid, resultReady, payload, grows⟩ :=
                SourceEqualityConstraintMemoAllocation.combine_correct stored (.live identity (head :: tail)) _ positiveValid
                  currentStored (positiveReady _ rfl)
              rw [actual]
              refine ⟨result, done, afterValid, resultReady, ?_, grows_trans positiveGrows grows,
                fun _ => combine_roundtrip _ _ _ payload⟩
              rw [combine_classes _ _ _ payload]
              simp only [SourceCompactGuards.sourceEqualities, constraint, ← positiveClasses, Option.map_some,
                SourceEqualityInheritedPayload.classes, Value.payload, List.map_cons]

/-- The actual accessor completes with exact source classes, ready output, and allocation receipts. -/
theorem equalities_correct (stored : Value) (guard : SourceGuards.Guard Formula) (before : State)
    (valid : Valid before) (storedReady : Ready before.constraints stored) :
    ∃ result, (equalities stored guard before).1 = .ok result ∧ Valid (equalities stored guard before).2 ∧
      Ready (equalities stored guard before).2.constraints result ∧
      SourceEqualityInheritedPayload.classes result.payload = SourceCompactGuards.sourceEqualities (constraint stored guard) ∧
      Grows before (equalities stored guard before).2 := by
  obtain ⟨result, done, afterValid, ready, classes, grows, _⟩ := equalities_full stored guard before valid storedReady
  exact ⟨result, done, afterValid, ready, classes, grows⟩

/-- An original constructor receipt connects actual accessor allocation to literal physical own readback. -/
theorem own_of_equalities (stored : Value) (guard : SourceGuards.Guard Formula) (before : State)
    (valid : Valid before) (storedReady : Ready before.constraints stored)
    (original : Option EqualityNormalize.Constraints) (cached : SourceEqualityGuardReadback.Cached original)
    (built : SourceEqualityPhysicalPayload.read original = .ok stored.payload)
    (result : Value) (done : (equalities stored guard before).1 = .ok result) :
    SourceEqualityPhysicalPayload.own (constraint stored guard) = .ok result.payload := by
  obtain ⟨actual, completed, _, _, classes, _, roundtrip⟩ := equalities_full stored guard before valid storedReady
  have same : actual = result := Except.ok.inj (completed.symm.trans done)
  subst actual
  rw [SourceEqualityPhysicalPayload.own, ← classes]
  exact roundtrip (read_roundtrip original cached stored.payload built)

end MicroCFTA.SourceEqualityAccessorAllocation
