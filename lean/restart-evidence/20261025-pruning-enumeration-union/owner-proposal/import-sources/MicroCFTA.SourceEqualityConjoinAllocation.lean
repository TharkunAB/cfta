import MicroCFTA.SourceEqualityAccessorAllocation
import MicroCFTA.SourceEqualityConstraintConstructors

/-!
# Allocation receipts for raw stored constraint conjunction

The source conjoins stored equality fields before any full equality accessor.
Completed combination retains exact physical constructor readback. Guard
conjunction uses the existing source merge. Runtime demand remains separate.
-/
namespace MicroCFTA.SourceEqualityConjoinAllocation
open SourceEqualityConstraintAllocation
open SourceEqualityConstraintMemoAllocation (State Valid Grows)

/-- A complete source constraint retains its allocated stored field and raw guard. -/
structure Constraint (Formula : Type) where
  stored : Value
  guard : SourceGuards.Guard Formula

/-- Read the raw stored field and guard without calling the full equality accessor. -/
def readback (value : Constraint Formula) : SourceSymbolicIndex.Constraint Formula :=
  SourceEqualityAccessorAllocation.constraint value.stored value.guard

/-- Demand an original stored field without extracting positive guard equalities. -/
def construct (equalities : Option EqualityNormalize.Constraints) (guard : SourceGuards.Guard Formula)
    (before : State) : Except String (Constraint Formula) × State :=
  let built := SourceEqualityConstraintAllocation.construct equalities before.constraints
  (built.1.map (fun stored => ⟨stored, guard⟩), { before with constraints := built.2 })

/-- An actual original constructor receipt derives cached class readback and literal physical reconstruction. -/
theorem original_of_receipt (value : Constraint Formula) (original : Option EqualityNormalize.Constraints)
    (cached : SourceEqualityGuardReadback.Cached original)
    (built : SourceEqualityPhysicalPayload.read original = .ok value.stored.payload) :
    SourceEqualityGuardReadback.Cached (readback value).equalities ∧
      SourceEqualityPhysicalPayload.read (readback value).equalities = .ok value.stored.payload := by
  have classes := read_classes original cached value.stored.payload built
  change SourceEqualityGuardReadback.Cached (SourceEqualityInheritedPayload.classes value.stored.payload) ∧
    SourceEqualityPhysicalPayload.read (SourceEqualityInheritedPayload.classes value.stored.payload) = .ok value.stored.payload
  rw [classes]
  exact ⟨cached, built⟩

/-- An original normalized stored field produces a ready constraint with exact raw constructor receipts. -/
theorem construct_complete (equalities : Option EqualityNormalize.Constraints)
    (cached : SourceEqualityGuardReadback.Cached equalities) (guard : SourceGuards.Guard Formula)
    (before : State) (valid : Valid before) :
    ∃ value after, construct equalities guard before = (.ok value, after) ∧ Valid after ∧
      Ready after.constraints value.stored ∧ readback value = ⟨equalities, guard⟩ ∧
      SourceEqualityGuardReadback.Cached (readback value).equalities ∧
      SourceEqualityPhysicalPayload.read equalities = .ok value.stored.payload ∧ Grows before after := by
  obtain ⟨stored, cache, done, _, ready, steps, built, classes⟩ :=
    SourceEqualityConstraintAllocation.construct_complete equalities cached before.constraints valid.constraints
  refine ⟨⟨stored, guard⟩, {before with constraints := cache}, ?_, valid.steps _ steps, ready, ?_, ?_, built,
    ⟨steps, Cache.extends_refl _, Cache.extends_refl _⟩⟩
  · simp only [construct, done, Except.map]
  · change (⟨SourceEqualityInheritedPayload.classes stored.payload, guard⟩ : SourceSymbolicIndex.Constraint Formula) = ⟨equalities, guard⟩
    rw [classes]
  · exact (original_of_receipt ⟨stored, guard⟩ equalities cached built).1

/-- Source conjunction combines only the raw stored fields and merges the original guards. -/
noncomputable def conjoin [DecidableEq (SourceGuards.Guard Formula)]
    (le : SourceGuards.Guard Formula → SourceGuards.Guard Formula → Bool)
    (first second : Constraint Formula) (before : State) : Except String (Constraint Formula) × State :=
  let built := SourceEqualityConstraintMemoAllocation.combine first.stored second.stored before
  (built.1.map (fun stored => ⟨stored, GuardConjunction.merge le first.guard second.guard⟩), built.2)

/-- A previously completed raw combination retains the entire operation state. -/
theorem conjoin_state_of_hit [DecidableEq (SourceGuards.Guard Formula)]
    (le : SourceGuards.Guard Formula → SourceGuards.Guard Formula → Bool)
    (first second : Constraint Formula) (before : State) (cell : SourceEqualityConstraintMemoAllocation.CombineCell)
    (present : before.combinations (first.stored.identity, second.stored.identity) = some cell) :
    (conjoin le first second before).2 = before :=
  SourceEqualityConstraintMemoAllocation.combine_state_of_hit first.stored second.stored before cell present

/-- Completed raw conjunction derives exact existing constructor readback and cached physical output. -/
theorem conjoin_correct [DecidableEq (SourceGuards.Guard Formula)]
    (le : SourceGuards.Guard Formula → SourceGuards.Guard Formula → Bool)
    (first second : Constraint Formula) (before : State) (valid : Valid before)
    (firstReady : Ready before.constraints first.stored) (secondReady : Ready before.constraints second.stored) :
    ∃ result, (conjoin le first second before).1 = .ok result ∧ Valid (conjoin le first second before).2 ∧
      Ready (conjoin le first second before).2.constraints result.stored ∧
      readback result = SourceEqualityConstraintConstructors.conjoin le (readback first) (readback second) ∧
      SourceEqualityGuardReadback.Cached (readback result).equalities ∧
      SourceEqualityPhysicalPayload.read (SourceEqualityConstraintConstructors.conjoin le (readback first) (readback second)).equalities =
        .ok result.stored.payload ∧ Grows before (conjoin le first second before).2 := by
  obtain ⟨stored, done, afterValid, ready, payload, grows⟩ :=
    SourceEqualityConstraintMemoAllocation.combine_correct first.stored second.stored before valid firstReady secondReady
  have classes := read_classes _ (SourceEqualityGuardReadback.combine_cached _ _) stored.payload payload
  have cached := SourceEqualityGuardReadback.combine_cached
    (SourceEqualityInheritedPayload.classes first.stored.payload) (SourceEqualityInheritedPayload.classes second.stored.payload)
  simp only [conjoin, done, Except.map]
  refine ⟨⟨stored, GuardConjunction.merge le first.guard second.guard⟩, rfl, afterValid, ready, ?_, ?_, payload, grows⟩
  · change (⟨SourceEqualityInheritedPayload.classes stored.payload, GuardConjunction.merge le first.guard second.guard⟩ :
      SourceSymbolicIndex.Constraint Formula) = ⟨_, _⟩
    rw [classes]
    rfl
  · change SourceEqualityGuardReadback.Cached (SourceEqualityInheritedPayload.classes stored.payload)
    rw [classes]
    exact cached

/-- Actual successful conjunction retains literal physical readback at its returned stored classes. -/
theorem result_readback [DecidableEq (SourceGuards.Guard Formula)]
    (le : SourceGuards.Guard Formula → SourceGuards.Guard Formula → Bool)
    (first second : Constraint Formula) (before : State) (valid : Valid before)
    (firstReady : Ready before.constraints first.stored) (secondReady : Ready before.constraints second.stored)
    (result : Constraint Formula) (done : (conjoin le first second before).1 = .ok result) :
    SourceEqualityGuardReadback.Cached (readback result).equalities ∧
      SourceEqualityPhysicalPayload.read (readback result).equalities = .ok result.stored.payload := by
  obtain ⟨actual, completed, _, _, same, cached, built, _⟩ := conjoin_correct le first second before valid firstReady secondReady
  have identical : actual = result := Except.ok.inj (completed.symm.trans done)
  subst actual
  exact ⟨cached, by rw [same]; exact built⟩

/-- Cached original fields give the existing source Boolean conjunction law for actual allocated output. -/
theorem conjoined [DecidableEq Formula] [DecidableEq (SourceGuards.Guard Formula)]
    (le : SourceGuards.Guard Formula → SourceGuards.Guard Formula → Bool)
    (formulas : SourceGuards.Formulas Formula) (solver : SourceGuards.Entailment Formula)
    (first second : Constraint Formula) (before : State) (valid : Valid before)
    (firstReady : Ready before.constraints first.stored) (secondReady : Ready before.constraints second.stored)
    (firstCached : SourceEqualityGuardReadback.Cached (readback first).equalities)
    (secondCached : SourceEqualityGuardReadback.Cached (readback second).equalities)
    (result : Constraint Formula) (done : (conjoin le first second before).1 = .ok result)
    (term : Language.Term (SourceObservations.Label Formula)) :
    SourceSymbolicIndex.acceptsConstraint formulas solver (readback result) term =
      (SourceSymbolicIndex.acceptsConstraint formulas solver (readback first) term &&
        SourceSymbolicIndex.acceptsConstraint formulas solver (readback second) term) := by
  obtain ⟨actual, completed, _, _, same, _, _, _⟩ := conjoin_correct le first second before valid firstReady secondReady
  have identical : actual = result := Except.ok.inj (completed.symm.trans done)
  subst actual
  rw [same]
  exact SourceEqualityConstraintConstructors.conjoined le formulas solver _ _
    (SourceEqualityGuardReadback.active firstCached) (SourceEqualityGuardReadback.active secondCached) term

end MicroCFTA.SourceEqualityConjoinAllocation
