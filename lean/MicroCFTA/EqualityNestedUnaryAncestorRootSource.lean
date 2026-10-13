import MicroCFTA.EqualityNestedUnaryAncestorRootTermination

/-!
# Preserve current target merges in the ancestor-root loop

The source computes and merges both snapshot projections before editing.
The represented four-row fragment derives that each current-policy merge
returns its exact projection and cache. The whole source iteration keeps
those calls and has the same actual result and cache as constructor work.
-/
namespace MicroCFTA.EqualityNestedUnaryAncestorRoot
open SourceGuards FullSyntax InternedConstructorTemplates InternedRecordCoherence
open InternedProbeProvenance InternedNestedFacts InternedNestedProvenance InternedEdgeResidency
open MergedPhysicalWarmup MergedSourceComparison MergedColdMerge
open EqualityNestedUnaryCarrier EqualityNestedUnaryProduct EqualityNestedUnarySchedule EqualityMergedTargetReadback
open EqualityNestedUnaryAncestor EqualityNestedUnaryAncestorState
noncomputable local instance : DecidableEq ConstraintKey := by classical exact inferInstance

/-- Compute the actual ancestor projection and run the current target merger. -/
noncomputable def target (clear : ConstraintKey → Bool) (top : ConstraintKey) (comparison : Nat)
    (root : Value (Fin symbols) ConstraintKey) : Action (Fin symbols) ConstraintKey (Value (Fin symbols) ConstraintKey) :=
  MergedColdMerge.bind (MergedColdMerge.work (makeUnion (projected root)))
    (execute MergedSourceGrouping.groups clear top comparison)

/-- Actual source projection and merging preserve the exact result and cache in this derived fragment. -/
theorem target_eq (parent leaf : Fin symbols) (rows : Fin count → Node initial)
    (tags : Fin count → Fin symbols × ConstraintKey) (values : ValuesAt symbols count)
    (small : (SourceLeafRowProgress.basis initial).length ≤ 2)
    (root : Value (Fin symbols) ConstraintKey) (state : State (Fin symbols) ConstraintKey)
    (facts : Facts state) (prepared : Prepared state) (stored : Stored tags values state root)
    (represented : Represents parent leaf state rows values)
    (clear : ConstraintKey → Bool) (top : ConstraintKey) (comparison : Nat) :
    target clear top comparison root state = MergedColdMerge.work (makeUnion (projected root)) state := by
  obtain ⟨bound, output, after, done, extension, available, normal, shape⟩ :=
    project_complete parent leaf rows tags values state facts prepared root stored represented
  have completed := done bound (Nat.le_refl _)
  have fixed := EqualityNestedUnaryBound.merge_fixed parent leaf _ output small shape normal
    after extension.facts extension.prepared available clear top comparison
  simp only [target, MergedColdMerge.bind, completed, Result.bind, fixed]

/-- Source target merges occur before both ordered physical ancestor edits. -/
noncomputable def sourceStep (clear : ConstraintKey → Bool) (top : ConstraintKey) (comparison : Nat)
    (roots : Roots symbols) : Action (Fin symbols) ConstraintKey (Roots symbols) :=
  MergedColdMerge.bind (target clear top comparison roots.1) fun first =>
    MergedColdMerge.bind (target clear top comparison roots.2) fun second =>
      MergedColdMerge.bind (MergedColdMerge.work (EqualityNestedUnaryAncestorEdit.nodeWork second roots.1)) fun newLeft =>
        MergedColdMerge.bind (MergedColdMerge.work (EqualityNestedUnaryAncestorEdit.nodeWork first roots.2)) fun newRight =>
          MergedColdMerge.pure (newLeft, newRight)

/-- The complete source pass retains every constructor effect and current merge result exactly. -/
theorem sourceStep_eq (parent leaf : Fin symbols) (tags : Tags symbols left right)
    (small : (SourceLeafRowProgress.basis initial).length ≤ 2)
    (rows : Projected initial left right) (roots : Roots symbols)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state) (prepared : Prepared state)
    (represented : RepresentsRoots parent leaf tags rows state roots)
    (clear : ConstraintKey → Bool) (top : ConstraintKey) (comparison : Nat) :
    sourceStep clear top comparison roots state = MergedColdMerge.work (stepWork roots) state := by
  obtain ⟨values, firstStored, secondStored, leftValid, rightValid⟩ := represented
  obtain ⟨bound, first, afterFirst, firstDone, firstExtension, _⟩ :=
    project_complete parent leaf rows.1 tags.1 values.1 state facts prepared roots.1 firstStored leftValid
  have firstRun := Result.done.inj (firstDone bound (Nat.le_refl _))
  have exactFirst : run (makeUnion (projected roots.1)) state = (first, afterFirst) := Prod.ext firstRun.1 firstRun.2
  have firstTarget := target_eq parent leaf rows.1 tags.1 values.1 small roots.1 state facts prepared
    firstStored leftValid clear top comparison
  have rightStored := stored_grows tags.2 values.2 state afterFirst facts.coherent.valid firstExtension.growth roots.2 secondStored
  have representedRight := represents_grows parent leaf state afterFirst firstExtension rows.2 values.2 rightValid
  have secondTarget := target_eq parent leaf rows.2 tags.2 values.2 small roots.2 afterFirst firstExtension.facts
    firstExtension.prepared rightStored representedRight clear top comparison
  simp only [sourceStep, MergedColdMerge.bind, firstTarget, MergedColdMerge.work, exactFirst, Result.bind,
    secondTarget, stepWork, run_bind, MergedColdMerge.pure, run]

/-- The source iteration keeps its target merges and tests actual ancestor references. -/
noncomputable def sourceIterate (clear : ConstraintKey → Bool) (top : ConstraintKey) (comparison : Nat) :
    Nat → Roots symbols → Action (Fin symbols) ConstraintKey (Option (Roots symbols))
  | 0, _ => MergedColdMerge.pure none
  | fuel + 1, roots => by
    classical
    exact MergedColdMerge.bind (sourceStep clear top comparison roots) fun next =>
      if Same next roots then MergedColdMerge.pure (some next) else sourceIterate clear top comparison fuel next

/-- Actual source iteration and constructor replay agree at every fuel and every returned cache. -/
theorem sourceIterate_eq (parent leaf : Fin symbols) (tags : Tags symbols left right)
    (small : (SourceLeafRowProgress.basis initial).length ≤ 2)
    (fuel : Nat) (rows : Projected initial left right) (roots : Roots symbols)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state) (prepared : Prepared state)
    (represented : RepresentsRoots parent leaf tags rows state roots)
    (clear : ConstraintKey → Bool) (top : ConstraintKey) (comparison : Nat) :
    sourceIterate clear top comparison fuel roots state = MergedColdMerge.work (iterate fuel roots) state := by
  classical
  induction fuel generalizing rows roots state with
  | zero => rfl
  | succ fuel ih =>
    have pass := sourceStep_eq parent leaf tags small rows roots state facts prepared represented clear top comparison
    have checked := step_correct parent leaf tags rows roots state facts prepared represented
    let actual := run (stepWork roots) state
    have later := ih (EqualityFixedProjectionTermination.step (Join initial) rows) actual.1 actual.2
      checked.1.facts checked.1.prepared checked.2
    simp only [sourceIterate, MergedColdMerge.bind, pass, MergedColdMerge.work, Result.bind, iterate, run_bind]
    by_cases same : Same actual.1 roots
    · dsimp only [actual] at same
      simp only [ite_eq_left same, MergedColdMerge.pure, run]
    · dsimp only [actual] at same
      simpa only [ite_eq_right same, actual, MergedColdMerge.work] using later

/-- Both actual forest roots reach a source fixed point within the derived finite row bound. -/
theorem source_termination (parent leaf : Fin symbols) (tags : Tags symbols left right)
    (small : (SourceLeafRowProgress.basis initial).length ≤ 2)
    (rows : Projected initial left right) (roots : Roots symbols)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state) (prepared : Prepared state)
    (represented : RepresentsRoots parent leaf tags rows state roots)
    (clear : ConstraintKey → Bool) (top : ConstraintKey) (comparison : Nat) :
    ∃ fuel output after, ∃ current : Projected initial left right,
      fuel ≤ 4 * (left + right) + 2 ∧
      (∀ larger, fuel ≤ larger → sourceIterate clear top comparison larger roots state = .done (some output) after) ∧
      Extension state after ∧ RepresentsRoots parent leaf tags current after output ∧
      sourceStep clear top comparison output after = .done output after := by
  obtain ⟨fuel, output, after, current, bound, completed, extension, valid, fixed⟩ :=
    termination parent leaf tags small rows roots state facts prepared represented
  refine ⟨fuel, output, after, current, bound, ?_, extension, valid, ?_⟩
  · intro larger enough
    rw [sourceIterate_eq parent leaf tags small larger rows roots state facts prepared represented clear top comparison]
    simp only [MergedColdMerge.work, iterate_stable fuel larger enough roots output state after completed]
  · rw [sourceStep_eq parent leaf tags small current output after extension.facts extension.prepared valid clear top comparison]
    simp only [MergedColdMerge.work, fixed]

end MicroCFTA.EqualityNestedUnaryAncestorRoot
