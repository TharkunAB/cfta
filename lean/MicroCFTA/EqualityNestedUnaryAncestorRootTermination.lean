import MicroCFTA.EqualityNestedUnaryAncestorRootIdentity

/-!
# Bounded iteration of the actual unary ancestor roots

Each pass reads both original projections and edits both ancestors.
A changing physical root pass changes the finite generated row state.
An early physical stop is permitted when ancestor normalization hides an
indexed change. The returned roots still form an allocation-free fixed point.
-/
namespace MicroCFTA.EqualityNestedUnaryAncestorRoot
open SourceGuards FullSyntax InternedConstructorTemplates InternedRecordCoherence
open InternedProbeProvenance InternedNestedFacts InternedNestedProvenance InternedEdgeResidency
open MergedPhysicalWarmup MergedSourceComparison MergedColdMerge
open EqualityNestedUnaryCarrier EqualityNestedUnaryProduct EqualityNestedUnarySchedule EqualityMergedTargetReadback
noncomputable local instance : DecidableEq ConstraintKey := by classical exact inferInstance

/-- Repeat actual ancestor work until the ordered root identities are unchanged. -/
noncomputable def iterate : Nat → Roots symbols → Work (Fin symbols) ConstraintKey (Option (Roots symbols))
  | 0, _ => .pure none
  | fuel + 1, roots => by
    classical
    exact (stepWork roots).bind fun next => if Same next roots then .pure (some next) else iterate fuel next

/-- A bounded generated-row run supplies a completed actual ancestor loop and a physical fixed point. -/
theorem run_refines (parent leaf : Fin symbols) (tags : Tags symbols left right)
    (fuel : Nat) (rows result : Projected initial left right)
    (modelDone : EqualityFixedProjectionTermination.run (Join initial) fuel rows = some result)
    (roots : Roots symbols) (state : State (Fin symbols) ConstraintKey)
    (facts : Facts state) (prepared : Prepared state)
    (represented : RepresentsRoots parent leaf tags rows state roots) :
    ∃ output after, ∃ current : Projected initial left right, run (iterate fuel roots) state = (some output, after) ∧ Extension state after ∧
      RepresentsRoots parent leaf tags current after output ∧ run (stepWork output) after = (output, after) := by
  classical
  induction fuel generalizing rows roots state with
  | zero => simp only [EqualityFixedProjectionTermination.run, reduceCtorEq] at modelDone
  | succ fuel ih =>
    let passed := run (stepWork roots) state
    have checked := step_correct parent leaf tags rows roots state facts prepared represented
    change Extension state passed.2 ∧
      RepresentsRoots parent leaf tags (EqualityFixedProjectionTermination.step (Join initial) rows) passed.2 passed.1 at checked
    by_cases same : Same passed.1 roots
    · dsimp only [passed] at same
      refine ⟨passed.1, passed.2, EqualityFixedProjectionTermination.step (Join initial) rows, ?_, checked.1, checked.2, ?_⟩
      · simp only [iterate, run_bind, ite_eq_left same, run]
        rfl
      · exact unchanged_fixed parent leaf tags rows roots passed.1 state passed.2 facts checked.1
          represented checked.2 rfl same
    · dsimp only [passed] at same
      have changed := changed_rows parent leaf tags rows roots passed.1 state passed.2 facts checked.1 represented checked.2 same
      have later : EqualityFixedProjectionTermination.run (Join initial) fuel
          (EqualityFixedProjectionTermination.step (Join initial) rows) = some result := by
        simpa only [EqualityFixedProjectionTermination.run, ite_eq_right changed] using modelDone
      obtain ⟨output, after, current, done, extension, valid, fixed⟩ :=
        ih _ later passed.1 passed.2 checked.1.facts checked.1.prepared checked.2
      refine ⟨output, after, current, ?_, checked.1.trans extension, valid, fixed⟩
      simpa only [iterate, run_bind, ite_eq_right same] using done

/-- The whole ancestor-root loop finishes within four rows per original occurrence plus two tests. -/
theorem termination (parent leaf : Fin symbols) (tags : Tags symbols left right)
    (small : (SourceLeafRowProgress.basis initial).length ≤ 2)
    (rows : Projected initial left right) (roots : Roots symbols)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state) (prepared : Prepared state)
    (represented : RepresentsRoots parent leaf tags rows state roots) :
    ∃ fuel output after, ∃ current : Projected initial left right, fuel ≤ 4 * (left + right) + 2 ∧
      run (iterate fuel roots) state = (some output, after) ∧ Extension state after ∧
      RepresentsRoots parent leaf tags current after output ∧ run (stepWork output) after = (output, after) := by
  obtain ⟨fuel, result, bound, done, _⟩ := projected_bound initial left right small rows
  obtain ⟨output, after, current, completed, extension, valid, fixed⟩ :=
    run_refines parent leaf tags fuel rows result done roots state facts prepared represented
  exact ⟨fuel, output, after, current, bound, completed, extension, valid, fixed⟩

/-- Additional loop fuel leaves every completed root and the actual returned cache unchanged. -/
theorem iterate_stable (fuel larger : Nat) (enough : fuel ≤ larger) (roots output : Roots symbols)
    (state after : State (Fin symbols) ConstraintKey)
    (done : run (iterate fuel roots) state = (some output, after)) :
    run (iterate larger roots) state = (some output, after) := by
  classical
  induction fuel generalizing larger roots state with
  | zero => simp only [iterate, run, Prod.mk.injEq, reduceCtorEq, false_and] at done
  | succ fuel ih =>
    cases larger with
    | zero => omega
    | succ larger =>
      let passed := run (stepWork roots) state
      by_cases same : Same passed.1 roots
      · dsimp only [passed] at same
        simpa only [iterate, run_bind, ite_eq_left same, run] using done
      · dsimp only [passed] at same
        have next : run (iterate fuel passed.1) passed.2 = (some output, after) := by
          simpa only [iterate, run_bind, ite_eq_right same] using done
        have later := ih larger (by omega) passed.1 passed.2 next
        simpa only [iterate, run_bind, ite_eq_right same] using later

end MicroCFTA.EqualityNestedUnaryAncestorRoot
