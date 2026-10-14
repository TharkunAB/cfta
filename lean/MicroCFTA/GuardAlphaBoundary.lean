import MicroCFTA.FullGuardPrune

/-!
# Sound solver uncertainty need not be alpha-invariant

The source signatures can omit a constructor name that affects fresh-name
allocation. A sound incomplete solver can decide only one of those spellings.
This changes confirmed Yes/Unknown behavior, not mathematical entailment.
-/
namespace MicroCFTA.GuardAlphaBoundary
open SourceGuards SourceObservations FullSyntax

/-- This solver proves only Top conclusions with one selected fresh-name spelling. -/
def solver : SourceGuards.Entailment Formula := fun bindings _ consequent =>
  if consequent = .top && bindings.any (fun binding => binding.1 == "__cfta_actual_0") then
    .yes else .unknown

/-- The solver is sound for every interpretation and every declared environment domain. -/
theorem solver_sound (model : Interpretation Value)
    (admitted : List (String × String) → (String → Value) → Prop) : SourceEntailment.Sound model admitted solver := by
  intro bindings antecedent consequent
  unfold solver
  split
  · rename_i selected
    have top : consequent = .top := by simpa only [decide_eq_true_eq] using (Bool.and_eq_true_iff.mp selected).1
    subst consequent
    intro env _ _
    simp [Holds]
  · trivial

/-- Both actuals are leaves. Their different annotations make their identities unambiguous. -/
def observations (blocked : Bool) : Observations Formula := fun path =>
  match path with
  | [0] => some ⟨"same", .top, .leaf⟩
  | [1] => some ⟨"same", .not .bottom, .leaf⟩
  | [2] => some ⟨"left", .top, .leaf⟩
  | [3] => some ⟨"right", .top, .leaf⟩
  | [4] => some ⟨if blocked then "__cfta_actual_0" else "ordinary", .top, .leaf⟩
  | _ => none

/-- The last constructor name is not a structural read of this guard. -/
def guard : SourceGuards.Guard Formula :=
  .substitute [⟨[0], [2]⟩, ⟨[1], [3]⟩] (.satisfies [4] .top)

/-- Both sparse views come from complete finite terms with the stated five leaf children. -/
def term (blocked : Bool) : Language.Term (Label Formula) :=
  .node ("root", .top)
    [.node ("same", .top) [], .node ("same", .not .bottom) [],
     .node ("left", .top) [], .node ("right", .top) [],
     .node ((if blocked then "__cfta_actual_0" else "ordinary"), .top) []]

private theorem actual_order : orderedPaths [[0], [1]] = [[0], [1]] := by
  change ([[0], [1]] : List Path).mergeSort _ = _
  exact List.mergeSort_of_pairwise (by decide +kernel)

private theorem used_order : orderedPaths [[0], [2], [1], [3], [4]] = [[0], [1], [2], [3], [4]] := by
  change ([[0], [2], [1], [3], [4]] : List Path).mergeSort _ = _
  simp [List.mergeSort, compare, List.compareLex, compareOfLessAndEq]

/-- The two source cells have identical semantic grouping signatures. -/
theorem same_signature : SourceReadAgreement.signature guard (observations false) =
    SourceReadAgreement.signature guard (observations true) := by
  funext path
  by_cases present : path ∈ paths guard
  · simp only [guard, paths, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl | rfl | rfl | rfl <;>
      simp [SourceReadAgreement.signature, guard, paths, sensitive, observations]
  · simp [SourceReadAgreement.signature, present]

/-- Fresh spelling changes, although the source actual identities and ambiguity set do not. -/
theorem allocated_tables (blocked : Bool) :
    substitutionValues SourceFormula.operations (observations blocked)
      (sameShape SourceFormula.operations (observations blocked) []) guard =
      ((if blocked then [([0], "__cfta_actual_1", "same"), ([1], "__cfta_actual_2", "same")]
        else [([0], "__cfta_actual_0", "same"), ([1], "__cfta_actual_1", "same")]), []) := by
  cases blocked <;>
    simp [guard, substitutionValues, actuals, actualPaths, allocated, conflicts, values,
      usedNames, paths, requirements, ambiguous, actual_order, used_order] <;> decide +kernel

/-- The fixture observations are the complete term observations at every guard read. -/
theorem observations_requested (blocked : Bool) (path : Path) (requested : path ∈ paths guard) :
    observations blocked path = observe (term blocked) path := by
  simp only [guard, paths, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at requested
  rcases requested with rfl | rfl | rfl | rfl | rfl <;>
    cases blocked <;> decide +kernel

/-- Complete-term equality produces the same unambiguous actual tables for these leaf fixtures. -/
theorem complete_tables (blocked : Bool) :
    substitutionValues SourceFormula.operations (observe (term blocked))
      (sameTerm SourceFormula.operations (term blocked) []) guard =
      ((if blocked then [([0], "__cfta_actual_1", "same"), ([1], "__cfta_actual_2", "same")]
        else [([0], "__cfta_actual_0", "same"), ([1], "__cfta_actual_1", "same")]), []) := by
  have reads : SourceReadAgreement.Reads guard (observations blocked) (observe (term blocked)) :=
    ⟨fun path member => congrArg (Option.map SourceGuards.Observed.refinement) (observations_requested blocked path member),
     fun path member => observations_requested blocked path (SourceReadAgreement.sensitive_requested guard path member)⟩
  have none : ambiguous (observations blocked) (sameShape SourceFormula.operations (observations blocked) []) guard = [] :=
    congrArg Prod.snd (allocated_tables blocked)
  have completeNone : ambiguous (observe (term blocked)) (sameShape SourceFormula.operations (observe (term blocked)) []) guard = [] :=
    (SourceIdentityReads.ambiguous_reads SourceFormula.operations guard _ _ reads).symm.trans none
  rw [← ActualQuotient.unambiguous_tables_equal SourceFormula.operations (term blocked) guard completeNone]
  rw [← SourceIdentityReads.tables_reads SourceFormula.operations guard _ _ reads
    (SourceIdentityReads.usedNames_reads SourceFormula.operations guard _ _ (observations_requested blocked))]
  exact allocated_tables blocked

/-- The actual source sparse evaluator returns Yes for one cell and Unknown for the other. -/
theorem verdicts_differ :
    evaluateGuardWithShape SourceFormula.operations solver (observations false) guard = .yes ∧
    evaluateGuardWithShape SourceFormula.operations solver (observations true) guard = .unknown := by
  constructor
  all_goals
    unfold evaluateGuardWithShape evaluateGuardWithSame
    rw [allocated_tables]
    simp only [Bool.false_eq_true, ↓reduceIte, guard, evaluateWith]
    decide +kernel

/-- The public complete-term evaluator also returns Yes and Unknown respectively. -/
theorem complete_verdicts_differ :
    evaluateGuard SourceFormula.operations solver guard (term false) = .yes ∧
    evaluateGuard SourceFormula.operations solver guard (term true) = .unknown := by
  constructor
  all_goals
    unfold evaluateGuard evaluateGuardWithSame
    rw [complete_tables]
    simp only [Bool.false_eq_true, ↓reduceIte, guard, evaluateWith]
    decide +kernel

/-- The callback accepts only valid entailments, yet equal source signatures need not give equal verdicts. -/
theorem sound_is_not_alpha_stable :
    SourceEntailment.Sound integerModel (fun _ _ => True) solver ∧
      SourceReadAgreement.signature guard (observations false) = SourceReadAgreement.signature guard (observations true) ∧
      evaluateGuardWithShape SourceFormula.operations solver (observations false) guard ≠
        evaluateGuardWithShape SourceFormula.operations solver (observations true) guard := by
  refine ⟨solver_sound _ _, same_signature, ?_⟩
  rw [verdicts_differ.1, verdicts_differ.2]
  decide

end MicroCFTA.GuardAlphaBoundary
