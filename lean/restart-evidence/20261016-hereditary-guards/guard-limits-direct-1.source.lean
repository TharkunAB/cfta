import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope

/-!
# Ordered raw guard limits

The four numeric components use the componentwise order.
Joining limits retains both input envelopes.
The common native step also retains the raw conjunction envelope.
Computed initial limits read finite stored fields and raw guard syntax.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardLimits
open EqualityNormalize SourceGuards
open SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope
open SourceCurrentAllocatedFiniteOrdinaryConstraintEnvelope (wordCount normalizedDepth OptionBounds)

/-- Every raw guard limit component can increase independently. -/
structure Le (first last : Limits) : Prop where
  /-- The stored path-occurrence limit increases. -/
  storedOccurrences : first.storedOccurrences ≤ last.storedOccurrences
  /-- The stored path-depth limit increases. -/
  storedDepth : first.storedDepth ≤ last.storedDepth
  /-- The raw guard-stage limit increases. -/
  guardStages : first.guardStages ≤ last.guardStages
  /-- The exposed Same path-depth limit increases. -/
  guardDepth : first.guardDepth ≤ last.guardDepth

/-- Empty raw metadata has no required numeric component. -/
def zero : Limits := ⟨0, 0, 0, 0⟩

/-- Joining takes the maximum of every component. -/
def join (first second : Limits) : Limits :=
  ⟨max first.storedOccurrences second.storedOccurrences, max first.storedDepth second.storedDepth,
    max first.guardStages second.guardStages, max first.guardDepth second.guardDepth⟩

/-- One native query admits retained fields and one source conjunction. -/
def step (limits : Limits) : Limits := join limits (conjoinLimits limits limits)

/-- Each vector is below itself. -/
theorem le_refl (limits : Limits) : Le limits limits := ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩

/-- Componentwise order composes. -/
theorem le_trans {first middle last : Limits} (left : Le first middle) (right : Le middle last) : Le first last :=
  ⟨Nat.le_trans left.storedOccurrences right.storedOccurrences, Nat.le_trans left.storedDepth right.storedDepth,
    Nat.le_trans left.guardStages right.guardStages, Nat.le_trans left.guardDepth right.guardDepth⟩

/-- Zero fits every vector. -/
theorem zero_le (limits : Limits) : Le zero limits := ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩

/-- A join retains its first vector. -/
theorem le_join_left (first second : Limits) : Le first (join first second) :=
  ⟨Nat.le_max_left _ _, Nat.le_max_left _ _, Nat.le_max_left _ _, Nat.le_max_left _ _⟩

/-- A join retains its second vector. -/
theorem le_join_right (first second : Limits) : Le second (join first second) :=
  ⟨Nat.le_max_right _ _, Nat.le_max_right _ _, Nat.le_max_right _ _, Nat.le_max_right _ _⟩

/-- A common upper vector bounds the join. -/
theorem join_le {first second last : Limits} (left : Le first last) (right : Le second last) : Le (join first second) last :=
  ⟨Nat.max_le.mpr ⟨left.storedOccurrences, right.storedOccurrences⟩,
    Nat.max_le.mpr ⟨left.storedDepth, right.storedDepth⟩,
    Nat.max_le.mpr ⟨left.guardStages, right.guardStages⟩,
    Nat.max_le.mpr ⟨left.guardDepth, right.guardDepth⟩⟩

/-- The native step retains the initial vector. -/
theorem step_ge (limits : Limits) : Le limits (step limits) := le_join_left _ _

/-- The native step covers the actual raw conjunction transformer. -/
theorem conjoin_le_step (limits : Limits) : Le (conjoinLimits limits limits) (step limits) := le_join_right _ _

private theorem nat_mono (f : Nat → Nat) (grows : ∀ n, f n ≤ f (n + 1)) {first last : Nat} (enough : first ≤ last) :
    f first ≤ f last := by
  induction last with
  | zero => have same : first = 0 := by omega; subst first; exact Nat.le_refl _
  | succ last ih =>
      by_cases same : first = last + 1
      · subst first; exact Nat.le_refl _
      · exact Nat.le_trans (ih (by omega)) (grows last)

/-- Longer words increase the finite alphabet word count. -/
theorem wordCount_depth_mono (alphabet : Nat) {first last : Nat} (enough : first ≤ last) :
    wordCount alphabet first ≤ wordCount alphabet last := by
  apply nat_mono _ _ enough
  intro depth
  induction depth with
  | zero => simp [wordCount]
  | succ depth ih => exact Nat.add_le_add_left (Nat.mul_le_mul_left alphabet ih) 1

/-- The normalizer depth envelope increases in both initial components. -/
theorem normalizedDepth_mono {firstCount lastCount firstDepth lastDepth : Nat}
    (counts : firstCount ≤ lastCount) (depths : firstDepth ≤ lastDepth) :
    normalizedDepth firstCount firstDepth ≤ normalizedDepth lastCount lastDepth :=
  Nat.mul_le_mul (by omega) (by omega)

/-- The normalized occurrence envelope increases in both initial components. -/
theorem normalizedOccurrences_mono {firstCount lastCount firstDepth lastDepth : Nat}
    (counts : firstCount ≤ lastCount) (depths : firstDepth ≤ lastDepth) :
    normalizedOccurrences firstCount firstDepth ≤ normalizedOccurrences lastCount lastDepth := by
  have alphabet := SourceCurrentAllocatedFiniteOrdinaryConstraintEnvelope.wordCount_mono
    (Nat.mul_le_mul counts depths) (normalizedDepth firstCount firstDepth)
  have lengths := wordCount_depth_mono (lastCount * lastDepth) (normalizedDepth_mono counts depths)
  exact Nat.mul_le_mul counts (Nat.le_trans alphabet lengths)

/-- Raw guard budgets increase with the exposed Same path depth. -/
theorem positiveBudget_depth_mono {firstDepth lastDepth : Nat} (depths : firstDepth ≤ lastDepth) (count : Nat) :
    (positiveBudget firstDepth count).1 ≤ (positiveBudget lastDepth count).1 ∧
      (positiveBudget firstDepth count).2 ≤ (positiveBudget lastDepth count).2 := by
  induction count with
  | zero => exact ⟨Nat.le_refl _, depths⟩
  | succ count ih => exact ⟨normalizedOccurrences_mono (Nat.add_le_add ih.1 ih.1) ih.2,
      normalizedDepth_mono (Nat.add_le_add ih.1 ih.1) ih.2⟩

/-- Raw conjunction envelopes increase with both initial vectors. -/
theorem conjoin_mono {first largerFirst second largerSecond : Limits}
    (left : Le first largerFirst) (right : Le second largerSecond) :
    Le (conjoinLimits first second) (conjoinLimits largerFirst largerSecond) :=
  ⟨normalizedOccurrences_mono (Nat.add_le_add left.storedOccurrences right.storedOccurrences)
      (Nat.max_le_max left.storedDepth right.storedDepth),
    normalizedDepth_mono (Nat.add_le_add left.storedOccurrences right.storedOccurrences)
      (Nat.max_le_max left.storedDepth right.storedDepth),
    Nat.mul_le_mul_left 2 (Nat.add_le_add left.guardStages right.guardStages),
    Nat.max_le_max left.guardDepth right.guardDepth⟩

/-- Joining increasing inputs preserves their order. -/
theorem join_mono {first largerFirst second largerSecond : Limits}
    (left : Le first largerFirst) (right : Le second largerSecond) :
    Le (join first second) (join largerFirst largerSecond) :=
  ⟨Nat.max_le_max left.storedOccurrences right.storedOccurrences, Nat.max_le_max left.storedDepth right.storedDepth,
    Nat.max_le_max left.guardStages right.guardStages, Nat.max_le_max left.guardDepth right.guardDepth⟩

/-- The common native step is monotone. -/
theorem step_mono {first last : Limits} (enough : Le first last) : Le (step first) (step last) :=
  join_mono enough (conjoin_mono enough enough)

/-- Effective-own path bounds increase with the initial raw vector. -/
theorem effective_mono {first last : Limits} (enough : Le first last) :
    (effectiveBudget first).1 ≤ (effectiveBudget last).1 ∧ (effectiveBudget first).2 ≤ (effectiveBudget last).2 := by
  have stages := positiveBudget_mono first.guardDepth enough.guardStages
  have depths := positiveBudget_depth_mono enough.guardDepth last.guardStages
  have positive := ⟨Nat.le_trans stages.1 depths.1, Nat.le_trans stages.2 depths.2⟩
  have occurrences := Nat.add_le_add enough.storedOccurrences positive.1
  have lengths := Nat.max_le_max enough.storedDepth positive.2
  exact ⟨normalizedOccurrences_mono occurrences lengths, normalizedDepth_mono occurrences lengths⟩

/-- A raw constraint bound remains valid in a larger vector. -/
theorem bounds_mono {first last : Limits} (constraint : SourceSymbolicIndex.Constraint Formula)
    (input : Bounds first constraint) (enough : Le first last) : Bounds last constraint := by
  refine ⟨?_, Nat.le_trans input.stages enough.guardStages, ?_⟩
  · intro classes done
    have current := input.stored classes done
    exact ⟨Nat.le_trans current.occurrences enough.storedOccurrences,
      fun paths member path present => Nat.le_trans (current.depth paths member path present) enough.storedDepth⟩
  · intro left right member
    have current := input.paths left right member
    exact ⟨Nat.le_trans current.1 enough.guardDepth, Nat.le_trans current.2 enough.guardDepth⟩

/-- The source Top field fits every vector. -/
theorem top_bounds (limits : Limits) : Bounds limits (SourceEqualityConstraintConstructors.top (Formula := Formula)) := by
  refine ⟨?_, Nat.zero_le _, ?_⟩
  · intro classes done
    cases done
    constructor <;> simp
  · intro left right member
    simp [GuardConjunction.atoms] at member

/-- Two equally bounded fields produce a field within the common native step. -/
theorem conjoin_step [DecidableEq (Guard Formula)] (le : Guard Formula → Guard Formula → Bool)
    (first second : SourceSymbolicIndex.Constraint Formula) (limits : Limits)
    (left : Bounds limits first) (right : Bounds limits second) :
    Bounds (step limits) (SourceEqualityConstraintConstructors.conjoin le first second) :=
  bounds_mono _ (SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope.conjoin le first second limits limits left right)
    (conjoin_le_step limits)

private def maximum {α : Type} (measure : α → Nat) (items : List α) : Nat := (items.map measure).foldr Nat.max 0

private theorem maximum_member {α : Type} (measure : α → Nat) (items : List α) (item : α) (member : item ∈ items) :
    measure item ≤ maximum measure items := by
  induction items with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih member) (Nat.le_max_right _ _)

private def atomDepth : Guard Formula → Nat
  | .same first second => max first.length second.length
  | _ => 0

/-- Initial limits read every literal stored path and exposed raw Same atom. -/
def of_constraint (constraint : SourceSymbolicIndex.Constraint Formula) : Limits :=
  let classes := constraint.equalities.getD []
  ⟨classes.flatten.length, maximum List.length classes.flatten, stages constraint.guard,
    maximum atomDepth (GuardConjunction.atoms constraint.guard)⟩

/-- The computed initial vector needs no normalization or accessor success premise. -/
theorem of_constraint_bounds (constraint : SourceSymbolicIndex.Constraint Formula) : Bounds (of_constraint constraint) constraint := by
  refine ⟨?_, Nat.le_refl _, ?_⟩
  · intro classes done
    have stored : constraint.equalities = some classes := done
    refine ⟨?_, ?_⟩
    · simp only [of_constraint, stored, Option.getD_some]
      exact Nat.le_refl _
    · intro paths member path present
      simpa only [of_constraint, stored, Option.getD_some] using
        maximum_member List.length classes.flatten path (List.mem_flatten.mpr ⟨paths, member, present⟩)
  · intro first second member
    have bound := maximum_member atomDepth (GuardConjunction.atoms constraint.guard) (.same first second) member
    exact ⟨Nat.le_trans (Nat.le_max_left _ _) bound, Nat.le_trans (Nat.le_max_right _ _) bound⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardLimits
