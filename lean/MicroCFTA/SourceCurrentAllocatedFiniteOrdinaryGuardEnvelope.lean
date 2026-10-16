import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryConstraintEnvelope

/-!
# Raw guard and stored-field envelopes

Stored equality occurrences and raw guard syntax use separate metrics.
The guard metric counts every outer atom and every conjunction fold step.
Actual positive extraction normalizes at each source stage.
The path model uses natural indices and does not establish signed Haskell conversion.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope
open EqualityNormalize SourceGuards

/-- The occurrence bound after one actual normalization. -/
def normalizedOccurrences (occurrences depth : Nat) : Nat :=
  occurrences * SourceCurrentAllocatedFiniteOrdinaryConstraintEnvelope.wordCount (occurrences * depth) (SourceCurrentAllocatedFiniteOrdinaryConstraintEnvelope.normalizedDepth occurrences depth)

mutual
/-- Every atom costs one stage; Top contributes no atom or normalization. -/
def stages : Guard Formula → Nat
  | .top => 0
  | .and parts => listStages parts
  | _ => 1

/-- Each actual right-fold conjunction step adds one stage. -/
def listStages : List (Guard Formula) → Nat
  | [] => 0
  | first :: rest => stages first + listStages rest + 1
end

/-- Only Same paths exposed by the outer conjunction affect positive extraction. -/
def SamePaths (depth : Nat) (guard : Guard Formula) : Prop :=
  ∀ left right, .same left right ∈ GuardConjunction.atoms guard →
    left.length ≤ depth ∧ right.length ≤ depth

/-- This conservative binary transformer covers each actual normalization stage. -/
def positiveBudget (depth : Nat) : Nat → Nat × Nat
  | 0 => (2, depth)
  | count + 1 =>
      let previous := positiveBudget depth count
      (normalizedOccurrences (previous.1 + previous.1) previous.2,
        SourceCurrentAllocatedFiniteOrdinaryConstraintEnvelope.normalizedDepth (previous.1 + previous.1) previous.2)

private theorem wordCount_positive (alphabet depth : Nat) : 1 ≤ SourceCurrentAllocatedFiniteOrdinaryConstraintEnvelope.wordCount alphabet depth := by
  cases depth <;> simp [SourceCurrentAllocatedFiniteOrdinaryConstraintEnvelope.wordCount]

private theorem normalize_increases (occurrences depth : Nat) :
    occurrences ≤ normalizedOccurrences occurrences depth ∧ depth ≤ SourceCurrentAllocatedFiniteOrdinaryConstraintEnvelope.normalizedDepth occurrences depth := by
  constructor
  · exact Nat.le_mul_of_pos_right _ (wordCount_positive _ _)
  · simp only [SourceCurrentAllocatedFiniteOrdinaryConstraintEnvelope.normalizedDepth]
    have := Nat.le_mul_of_pos_right (depth + 1) (show 0 < occurrences + 1 by omega)
    omega

/-- More raw guard stages give a conservative positive-extraction budget. -/
theorem positiveBudget_mono (depth : Nat) {first last : Nat} (enough : first ≤ last) :
    (positiveBudget depth first).1 ≤ (positiveBudget depth last).1 ∧
      (positiveBudget depth first).2 ≤ (positiveBudget depth last).2 := by
  have step (count : Nat) : (positiveBudget depth count).1 ≤ (positiveBudget depth (count + 1)).1 ∧
      (positiveBudget depth count).2 ≤ (positiveBudget depth (count + 1)).2 := by
    have grown := normalize_increases ((positiveBudget depth count).1 + (positiveBudget depth count).1)
      (positiveBudget depth count).2
    exact ⟨Nat.le_trans (Nat.le_add_right _ _) grown.1, grown.2⟩
  induction last with
  | zero =>
      have same : first = 0 := by omega
      subst first
      exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | succ count ih =>
      by_cases same : first = count + 1
      · subst first
        exact ⟨Nat.le_refl _, Nat.le_refl _⟩
      · have previous := ih (by omega)
        exact ⟨Nat.le_trans previous.1 (step count).1, Nat.le_trans previous.2 (step count).2⟩

private theorem option_weaken {firstCount lastCount firstDepth lastDepth : Nat} {classes : Option Constraints}
    (input : SourceCurrentAllocatedFiniteOrdinaryConstraintEnvelope.OptionBounds firstCount firstDepth classes)
    (counts : firstCount ≤ lastCount) (depths : firstDepth ≤ lastDepth) :
    SourceCurrentAllocatedFiniteOrdinaryConstraintEnvelope.OptionBounds lastCount lastDepth classes := by
  intro output done
  have before := input output done
  exact ⟨Nat.le_trans before.occurrences counts,
    fun paths member path included => Nat.le_trans (before.depth paths member path included) depths⟩

private theorem empty_bound (occurrences depth : Nat) : SourceCurrentAllocatedFiniteOrdinaryConstraintEnvelope.OptionBounds occurrences depth (some []) := by
  intro output done
  cases done
  constructor <;> simp

private def GuardGoal (guard : Guard Formula) : Prop :=
  ∀ depth, SamePaths depth guard → ∀ output, SourceCompactGuards.positiveNormalized guard = some output →
    SourceCurrentAllocatedFiniteOrdinaryConstraintEnvelope.OptionBounds (positiveBudget depth (stages guard)).1 (positiveBudget depth (stages guard)).2 output

private def ListGoal (guards : List (Guard Formula)) : Prop :=
  ∀ depth, (∀ guard ∈ guards, SamePaths depth guard) →
    ∀ output, SourceCompactGuards.positiveNormalizedList guards = some output →
      SourceCurrentAllocatedFiniteOrdinaryConstraintEnvelope.OptionBounds (positiveBudget depth (listStages guards)).1 (positiveBudget depth (listStages guards)).2 output

private theorem extraction (guard : Guard Formula) : GuardGoal guard := by
  induction guard using Guard.rec (motive_2 := fun guards => ListGoal guards) with
  | top =>
      intro depth _ output done
      have same : some [] = output := Option.some.inj done
      subst output
      exact empty_bound _ _
  | same left right =>
      intro depth paths output done
      by_cases distinct : left ≠ right
      · have same : SourceCompactGuards.normalize [[left, right]] = output := by
          simpa [SourceCompactGuards.positiveNormalized, distinct] using done
        subst output
        have located := paths left right (by simp [GuardConjunction.atoms])
        apply (SourceCurrentAllocatedFiniteOrdinaryConstraintEnvelope.normalize [[left, right]] 4 depth ?_).bounds
        constructor
        · simp
        · simpa using located
      · simp [SourceCompactGuards.positiveNormalized, distinct] at done
  | and parts ih =>
      intro depth paths output done
      apply ih depth _ output done
      intro guard member left right present
      exact paths left right (by simpa only [GuardConjunction.atoms] using List.mem_flatMap.mpr ⟨guard, member, present⟩)
  | bottom | entails _ _ | satisfies _ _ | holds _ _ | substitute _ _ _ | not _ _ | or _ _ =>
      intro depth _ output done
      simp [SourceCompactGuards.positiveNormalized] at done
  | nil =>
      intro depth _ output done
      have same : some [] = output := Option.some.inj done
      subst output
      exact empty_bound _ _
  | cons first rest ih ir =>
      intro depth paths output done
      cases head : SourceCompactGuards.positiveNormalized first with
      | none => simp [SourceCompactGuards.positiveNormalizedList, head] at done
      | some initial =>
          cases tail : SourceCompactGuards.positiveNormalizedList rest with
          | none => simp [SourceCompactGuards.positiveNormalizedList, head, tail] at done
          | some remaining =>
              have same : SourceCompactGuards.combineEqualities initial remaining = output := by
                simpa [SourceCompactGuards.positiveNormalizedList, head, tail] using done
              subst output
              let common := stages first + listStages rest
              have left := ih depth (paths first List.mem_cons_self) initial head
              have right := ir depth (fun guard member => paths guard (List.mem_cons_of_mem first member)) remaining tail
              have leftEnough := positiveBudget_mono depth (show stages first ≤ common by dsimp [common]; omega)
              have rightEnough := positiveBudget_mono depth (show listStages rest ≤ common by dsimp [common]; omega)
              have combined := (SourceCurrentAllocatedFiniteOrdinaryConstraintEnvelope.combine initial remaining
                (option_weaken left leftEnough.1 leftEnough.2)
                (option_weaken right rightEnough.1 rightEnough.2)).bounds
              simpa only [listStages, positiveBudget, common, normalizedOccurrences, Nat.max_self] using combined

/-- The actual staged positive accessor derives bounds from raw syntax alone. -/
theorem positive_bounds (guard : Guard Formula) (count depth : Nat)
    (bounded : stages guard ≤ count) (paths : SamePaths depth guard)
    (output : Option Constraints) (done : SourceCompactGuards.positiveNormalized guard = some output) :
    SourceCurrentAllocatedFiniteOrdinaryConstraintEnvelope.OptionBounds (positiveBudget depth count).1 (positiveBudget depth count).2 output := by
  have initial := extraction guard depth paths output done
  have enough := positiveBudget_mono depth bounded
  exact option_weaken initial enough.1 enough.2

private theorem atom_stages (guard : Guard Formula) :
    ∀ atom ∈ GuardConjunction.atoms guard, stages atom = 1 := by
  induction guard using Guard.rec
    (motive_2 := fun guards => ∀ guard ∈ guards, ∀ atom ∈ GuardConjunction.atoms guard, stages atom = 1) with
  | top => simp [GuardConjunction.atoms]
  | and parts ih =>
      intro atom member
      simp only [GuardConjunction.atoms] at member
      obtain ⟨guard, present, member⟩ := List.mem_flatMap.mp member
      exact ih guard present atom member
  | bottom | same _ _ | entails _ _ | satisfies _ _ | holds _ _ | substitute _ _ _ | not _ _ | or _ _ =>
      intro atom member
      simp only [GuardConjunction.atoms, List.mem_singleton] at member
      subst atom
      rfl
  | nil => rename_i guard member atom present; simp at member
  | cons first rest ih ir =>
      rename_i guard member atom present
      rcases List.mem_cons.mp member with rfl | member
      · exact ih atom present
      · exact ir guard member atom present

private theorem atoms_length (guard : Guard Formula) : (GuardConjunction.atoms guard).length ≤ stages guard := by
  induction guard using Guard.rec
    (motive_2 := fun guards => (guards.flatMap GuardConjunction.atoms).length ≤ listStages guards) with
  | top => simp [GuardConjunction.atoms, stages]
  | and parts ih => simpa only [GuardConjunction.atoms, stages] using ih
  | bottom | same _ _ | entails _ _ | satisfies _ _ | holds _ _ | substitute _ _ _ | not _ _ | or _ _ =>
      simp [GuardConjunction.atoms, stages]
  | nil => simp [listStages]
  | cons first rest ih ir =>
      simp only [List.flatMap_cons, List.length_append, listStages]
      omega

private theorem conjoin_stages (guards : List (Guard Formula))
    (atomic : ∀ guard ∈ guards, stages guard ≤ 1) : stages (GuardConjunction.conjoin guards) ≤ 2 * guards.length := by
  have many : listStages guards ≤ 2 * guards.length := by
    induction guards with
    | nil => simp [listStages]
    | cons first rest ih =>
        have head := atomic first List.mem_cons_self
        have tail := ih (fun guard member => atomic guard (List.mem_cons_of_mem first member))
        simp only [listStages, List.length_cons]
        omega
  cases guards with
  | nil => simp [GuardConjunction.conjoin, stages]
  | cons first rest =>
      cases rest with
      | nil => simpa [GuardConjunction.conjoin] using Nat.le_trans (atomic first List.mem_cons_self) (by decide : 1 ≤ 2)
      | cons second rest => exact many

/-- Actual canonical guard conjunction has a bound from both original atom lists. -/
theorem merge_stages [DecidableEq (Guard Formula)] (le : Guard Formula → Guard Formula → Bool)
    (first second : Guard Formula) (firstCount secondCount : Nat)
    (left : stages first ≤ firstCount) (right : stages second ≤ secondCount) :
    stages (GuardConjunction.merge le first second) ≤ 2 * (firstCount + secondCount) := by
  let original := GuardConjunction.atoms first ++ GuardConjunction.atoms second
  let retained := GuardConjunction.canonical le original
  have count : retained.length ≤ original.length := by
    have bound := GuardConjunction.normalize_atoms_bound le (.and [first, second])
    simpa only [GuardConjunction.atoms_normalize, GuardConjunction.atoms, List.flatMap_cons,
      List.flatMap_nil, List.append_nil] using bound
  have atomic : ∀ guard ∈ retained, stages guard ≤ 1 := by
    intro guard member
    rcases List.mem_append.mp ((GuardConjunction.canonical_mem le original guard).mp member) with member | member
    · exact Nat.le_of_eq (atom_stages first guard member)
    · exact Nat.le_of_eq (atom_stages second guard member)
  have rawCount : original.length ≤ firstCount + secondCount := by
    have firstBound := Nat.le_trans (atoms_length first) left
    have secondBound := Nat.le_trans (atoms_length second) right
    simpa only [original, List.length_append] using Nat.add_le_add firstBound secondBound
  have final := Nat.le_trans (conjoin_stages retained atomic) (Nat.mul_le_mul_left 2 (Nat.le_trans count rawCount))
  simpa only [GuardConjunction.merge, GuardConjunction.normalize, GuardConjunction.atoms,
    List.flatMap_cons, List.flatMap_nil, List.append_nil] using final

/-- No retained Same path is new to both original guard atom lists. -/
theorem merge_paths [DecidableEq (Guard Formula)] (le : Guard Formula → Guard Formula → Bool)
    (first second : Guard Formula) (firstDepth secondDepth : Nat)
    (left : SamePaths firstDepth first) (right : SamePaths secondDepth second) :
    SamePaths (max firstDepth secondDepth) (GuardConjunction.merge le first second) := by
  intro firstPath secondPath member
  rcases (GuardConjunction.merge_mem le first second _).mp member with member | member
  · have bounded := left firstPath secondPath member
    exact ⟨Nat.le_trans bounded.1 (Nat.le_max_left _ _), Nat.le_trans bounded.2 (Nat.le_max_left _ _)⟩
  · have bounded := right firstPath secondPath member
    exact ⟨Nat.le_trans bounded.1 (Nat.le_max_right _ _), Nat.le_trans bounded.2 (Nat.le_max_right _ _)⟩

/-- Stored fields and raw guard syntax retain separate numeric components. -/
structure Limits where
  /-- Raw stored path occurrences include duplicates. -/
  storedOccurrences : Nat
  /-- Every stored path satisfies this length bound. -/
  storedDepth : Nat
  /-- Outer atoms and actual conjunction steps satisfy this count bound. -/
  guardStages : Nat
  /-- Every exposed Same path satisfies this length bound. -/
  guardDepth : Nat

/-- This vector refers only to the current raw constraint fields. -/
structure Bounds (limits : Limits) (constraint : SourceSymbolicIndex.Constraint Formula) : Prop where
  /-- The current stored field satisfies the first two components. -/
  stored : SourceCurrentAllocatedFiniteOrdinaryConstraintEnvelope.OptionBounds limits.storedOccurrences limits.storedDepth constraint.equalities
  /-- The raw guard supplies its actual syntax-stage count. -/
  stages : stages constraint.guard ≤ limits.guardStages
  /-- Positive extraction uses only these exposed Same paths. -/
  paths : SamePaths limits.guardDepth constraint.guard

/-- The closed conjunction transformer uses only the two initial vectors. -/
def conjoinLimits (first second : Limits) : Limits :=
  let occurrences := first.storedOccurrences + second.storedOccurrences
  let depth := max first.storedDepth second.storedDepth
  ⟨normalizedOccurrences occurrences depth, SourceCurrentAllocatedFiniteOrdinaryConstraintEnvelope.normalizedDepth occurrences depth,
    2 * (first.guardStages + second.guardStages), max first.guardDepth second.guardDepth⟩

/-- Effective-own bounds include the actual staged positive accessor. -/
def effectiveBudget (limits : Limits) : Nat × Nat :=
  let positive := positiveBudget limits.guardDepth limits.guardStages
  let occurrences := limits.storedOccurrences + positive.1
  let depth := max limits.storedDepth positive.2
  (normalizedOccurrences occurrences depth, SourceCurrentAllocatedFiniteOrdinaryConstraintEnvelope.normalizedDepth occurrences depth)

/-- Literal raw conjunction derives the next vector without an output-bound premise. -/
theorem conjoin [DecidableEq (Guard Formula)] (le : Guard Formula → Guard Formula → Bool)
    (first second : SourceSymbolicIndex.Constraint Formula) (firstLimits secondLimits : Limits)
    (left : Bounds firstLimits first) (right : Bounds secondLimits second) :
    Bounds (conjoinLimits firstLimits secondLimits) (SourceEqualityConstraintConstructors.conjoin le first second) := by
  exact ⟨(SourceCurrentAllocatedFiniteOrdinaryConstraintEnvelope.combine first.equalities second.equalities left.stored right.stored).bounds,
    merge_stages le first.guard second.guard _ _ left.stages right.stages,
    merge_paths le first.guard second.guard _ _ left.paths right.paths⟩

/-- The effective field bound follows from the initial stored and syntax vector. -/
theorem effective (constraint : SourceSymbolicIndex.Constraint Formula) (limits : Limits)
    (input : Bounds limits constraint) :
    SourceCurrentAllocatedFiniteOrdinaryConstraintEnvelope.OptionBounds (effectiveBudget limits).1 (effectiveBudget limits).2
      (SourceCompactGuards.sourceEqualities constraint) := by
  have storedEnough : limits.storedOccurrences ≤ (effectiveBudget limits).1 ∧
      limits.storedDepth ≤ (effectiveBudget limits).2 := by
    have grown := normalize_increases (limits.storedOccurrences + (positiveBudget limits.guardDepth limits.guardStages).1)
      (max limits.storedDepth (positiveBudget limits.guardDepth limits.guardStages).2)
    exact ⟨Nat.le_trans (Nat.le_add_right _ _) grown.1, Nat.le_trans (Nat.le_max_left _ _) grown.2⟩
  cases found : SourceCompactGuards.positiveNormalized constraint.guard with
  | none =>
      simpa only [SourceCompactGuards.sourceEqualities, found] using option_weaken input.stored storedEnough.1 storedEnough.2
  | some output =>
      have positive := positive_bounds constraint.guard _ _ input.stages input.paths output found
      cases output with
      | none =>
          intro result done
          cases stored : constraint.equalities <;>
            simp [SourceCompactGuards.sourceEqualities, found, SourceCompactGuards.combineEqualities, stored] at done
      | some classes =>
          cases classes with
          | nil =>
              simpa only [SourceCompactGuards.sourceEqualities, found] using option_weaken input.stored storedEnough.1 storedEnough.2
          | cons first rest =>
              have combined := (SourceCurrentAllocatedFiniteOrdinaryConstraintEnvelope.combine constraint.equalities (some (first :: rest)) input.stored positive).bounds
              simpa only [SourceCompactGuards.sourceEqualities, found, effectiveBudget, normalizedOccurrences] using combined

/-- Actual allocated conjunction constructs the same result with derived raw and effective envelopes. -/
theorem conjoin_complete [DecidableEq (Guard Formula)] (le : Guard Formula → Guard Formula → Bool)
    (first second : SourceEqualityConjoinAllocation.Constraint Formula)
    (before : SourceEqualityConstraintMemoAllocation.State)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before)
    (firstReady : SourceEqualityConstraintAllocation.Ready before.constraints first.stored)
    (secondReady : SourceEqualityConstraintAllocation.Ready before.constraints second.stored)
    (firstLimits secondLimits : Limits)
    (left : Bounds firstLimits (SourceEqualityConjoinAllocation.readback first))
    (right : Bounds secondLimits (SourceEqualityConjoinAllocation.readback second)) :
    ∃ result after, SourceEqualityConjoinAllocation.conjoin le first second before = (.ok result, after) ∧
      SourceEqualityConstraintMemoAllocation.Valid after ∧
      SourceEqualityConstraintAllocation.Ready after.constraints result.stored ∧
      SourceEqualityConstraintMemoAllocation.Grows before after ∧
      SourceEqualityGuardReadback.Cached (SourceEqualityConjoinAllocation.readback result).equalities ∧
      SourceEqualityPhysicalPayload.read (SourceEqualityConjoinAllocation.readback result).equalities = .ok result.stored.payload ∧
      Bounds (conjoinLimits firstLimits secondLimits) (SourceEqualityConjoinAllocation.readback result) ∧
      SourceCurrentAllocatedFiniteOrdinaryConstraintEnvelope.OptionBounds
        (effectiveBudget (conjoinLimits firstLimits secondLimits)).1
        (effectiveBudget (conjoinLimits firstLimits secondLimits)).2
        (SourceCompactGuards.sourceEqualities (SourceEqualityConjoinAllocation.readback result)) := by
  obtain ⟨result, done, afterValid, ready, same, cached, built, growth⟩ :=
    SourceEqualityConjoinAllocation.conjoin_correct le first second before valid firstReady secondReady
  have bounded : Bounds (conjoinLimits firstLimits secondLimits) (SourceEqualityConjoinAllocation.readback result) := by
    rw [same]
    exact conjoin le _ _ firstLimits secondLimits left right
  refine ⟨result, (SourceEqualityConjoinAllocation.conjoin le first second before).2,
    Prod.ext done rfl, afterValid, ready, growth, cached, ?_, bounded, effective _ _ bounded⟩
  rw [same]
  exact built

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope
