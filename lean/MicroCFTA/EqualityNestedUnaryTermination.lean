import MicroCFTA.EqualityNestedUnarySchedule

/-!
# A source-derived bound for the projected nested endpoint loop

The loop executes real unions, current-policy target merges, and nested
physical intersections. Its stop test compares the retained original node
identities. The generated child residual carrier supplies the finite
measure. This theorem stops at the indexed endpoint schedule boundary;
ancestor normalization and path admission remain separate.
-/
namespace MicroCFTA.EqualityNestedUnaryTermination
open SourceGuards FullSyntax InternedConstructorTemplates InternedRecordCoherence
open InternedProbeProvenance InternedNestedFacts InternedNestedProvenance InternedEdgeResidency
open InternedShallowHeap MergedPhysicalWarmup MergedSourceComparison MergedColdMerge
open EqualityNestedUnaryCarrier EqualityNestedUnaryChild EqualityNestedUnaryProduct EqualityMergedTargetReadback
open EqualityNestedUnaryMeet EqualityNestedUnarySchedule

noncomputable local instance : DecidableEq ConstraintKey := by classical exact inferInstance

/-- The source equality test compares the actual interned endpoint identities. -/
def Same (first second : Physical symbols left right) : Prop :=
  (∀ index, (first.1 index).referenceOf = (second.1 index).referenceOf) ∧
    (∀ index, (first.2 index).referenceOf = (second.2 index).referenceOf)

/-- Physical identity at every original position equals equality of its generated row predicates. -/
theorem same_iff (parent leaf : Fin symbols) (first second : Projected initial left right)
    (values others : Physical symbols left right) (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (firstValid : Represents parent leaf state first.1 values.1 ∧ Represents parent leaf state first.2 values.2)
    (secondValid : Represents parent leaf state second.1 others.1 ∧ Represents parent leaf state second.2 others.2) :
    Same values others ↔ first = second := by
  have position {count : Nat} (rows otherRows : Fin count → Node initial) (values others : ValuesAt symbols count)
      (valid : Represents parent leaf state rows values) (otherValid : Represents parent leaf state otherRows others) :
      (∀ index, (values index).referenceOf = (others index).referenceOf) ↔ rows = otherRows := by
    constructor
    · intro same
      funext index
      exact (identity_iff parent leaf (rows index) (otherRows index) (values index) (others index)
        (valid index).2.2 (otherValid index).2.2 (valid index).2.1 (otherValid index).2.1
        state facts (valid index).1 (otherValid index).1).mp (same index)
    · intro same index
      exact (identity_iff parent leaf (rows index) (otherRows index) (values index) (others index)
        (valid index).2.2 (otherValid index).2.2 (valid index).2.1 (otherValid index).2.1
        state facts (valid index).1 (otherValid index).1).mpr (congrFun same index)
  exact (and_congr (position _ _ _ _ firstValid.1 secondValid.1)
    (position _ _ _ _ firstValid.2 secondValid.2)).trans Prod.ext_iff.symm

/-- Execute the actual reciprocal endpoint pass until its interned identities stop changing. -/
noncomputable def run (clear : ConstraintKey → Bool) (top : ConstraintKey) (comparison : Nat) :
    Nat → Physical symbols left right → Action (Fin symbols) ConstraintKey (Physical symbols left right)
  | 0, _ => fun state => .failed .exhausted state
  | fuel + 1, values => by
      classical
      exact MergedColdMerge.bind (step clear top comparison values) fun next =>
        if Same next values then MergedColdMerge.pure next else run clear top comparison fuel next

/-- The actual cache-threaded loop refines each successful finite generated-row execution. -/
theorem run_refines (parent leaf : Fin symbols) (small : (SourceLeafRowProgress.basis initial).length ≤ 2)
    (clear : ConstraintKey → Bool) (top : ConstraintKey) (comparison fuel : Nat)
    (rows result : Projected initial left right)
    (modelDone : EqualityFixedProjectionTermination.run (Join initial) fuel rows = some result)
    (values : Physical symbols left right) (state : State (Fin symbols) ConstraintKey)
    (facts : Facts state) (prepared : Prepared state)
    (represented : Represents parent leaf state rows.1 values.1 ∧ Represents parent leaf state rows.2 values.2) :
    ∃ output after, run clear top comparison fuel values state = .done output after ∧ Extension state after ∧
      Represents parent leaf after result.1 output.1 ∧ Represents parent leaf after result.2 output.2 := by
  classical
  induction fuel generalizing rows values state with
  | zero => simp only [EqualityFixedProjectionTermination.run, reduceCtorEq] at modelDone
  | succ fuel ih =>
      obtain ⟨bound, next, middle, done, extension, leftValid, rightValid⟩ :=
        step_complete parent leaf rows values small state facts prepared represented clear top comparison
      have stepDone := done bound (Nat.le_refl _)
      have previous : Represents parent leaf middle rows.1 values.1 ∧ Represents parent leaf middle rows.2 values.2 :=
        ⟨represents_grows parent leaf state middle extension rows.1 values.1 represented.1,
          represents_grows parent leaf state middle extension rows.2 values.2 represented.2⟩
      have equality := same_iff parent leaf (EqualityFixedProjectionTermination.step (Join initial) rows) rows
        next values middle extension.facts ⟨leftValid, rightValid⟩ previous
      by_cases same : EqualityFixedProjectionTermination.step (Join initial) rows = rows
      · have resultEq : rows = result := by
          simpa only [EqualityFixedProjectionTermination.run, ite_eq_left same, Option.some.injEq] using modelDone
        subst result
        refine ⟨next, middle, ?_, extension, ?_, ?_⟩
        · simp only [run, MergedColdMerge.bind, stepDone, Result.bind, ite_eq_left (equality.mpr same), MergedColdMerge.pure]
        · simpa only [same] using leftValid
        · simpa only [same] using rightValid
      · have later : EqualityFixedProjectionTermination.run (Join initial) fuel
            (EqualityFixedProjectionTermination.step (Join initial) rows) = some result := by
          simpa only [EqualityFixedProjectionTermination.run, ite_eq_right same] using modelDone
        obtain ⟨output, after, nextDone, nextExtension, outputLeft, outputRight⟩ :=
          ih _ later next middle extension.facts extension.prepared ⟨leftValid, rightValid⟩
        refine ⟨output, after, ?_, extension.trans nextExtension, outputLeft, outputRight⟩
        simpa only [run, MergedColdMerge.bind, stepDone, Result.bind,
          ite_eq_right (fun equal => same (equality.mp equal))] using nextDone

/-- The nested physical endpoint loop stops within four generated rows per original occurrence plus two tests. -/
theorem termination (parent leaf : Fin symbols) (small : (SourceLeafRowProgress.basis initial).length ≤ 2)
    (clear : ConstraintKey → Bool) (top : ConstraintKey) (comparison : Nat)
    (rows : Projected initial left right) (values : Physical symbols left right)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state) (prepared : Prepared state)
    (represented : Represents parent leaf state rows.1 values.1 ∧ Represents parent leaf state rows.2 values.2) :
    ∃ fuel result output after, fuel ≤ 4 * (left + right) + 2 ∧
      run clear top comparison fuel values state = .done output after ∧ Extension state after ∧
      Represents parent leaf after result.1 output.1 ∧ Represents parent leaf after result.2 output.2 ∧
      EqualityFixedProjectionTermination.step (Join initial) result = result := by
  obtain ⟨fuel, result, bound, done, fixed⟩ := projected_bound initial left right small rows
  obtain ⟨output, after, actual, extension, outputLeft, outputRight⟩ :=
    run_refines parent leaf small clear top comparison fuel rows result done values state facts prepared represented
  exact ⟨fuel, result, output, after, bound, actual, extension, outputLeft, outputRight, fixed⟩

end MicroCFTA.EqualityNestedUnaryTermination
