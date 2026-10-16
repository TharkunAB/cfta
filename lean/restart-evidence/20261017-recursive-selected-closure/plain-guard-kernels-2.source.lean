import MicroCFTA.SourceCurrentUnconstrainedGuardClosure
import MicroCFTA.SourceEqualityNativeDemand

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option format.width 200

namespace MicroCFTA.PlainGuardIndependent
open SourceCurrentUnconstrainedGuardClosure SourceCompactGuards
open SourceEqualityConstraintAllocation
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "Operations" => SourceEqualityConstraintMemoAllocation.State
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula

private theorem conjoin_top [DecidableEq (SourceGuards.Guard FullSyntax.Formula)]
    (le : SourceGuards.Guard FullSyntax.Formula → SourceGuards.Guard FullSyntax.Formula → Bool)
    (left right : Guard) (leftCached : SourceEqualityGuardReadback.Cached left.equalities)
    (rightCached : SourceEqualityGuardReadback.Cached right.equalities)
    (leftPlain : SourceMemoGate.plain left = true) (rightPlain : SourceMemoGate.plain right = true) :
    SourceEqualityConstraintConstructors.conjoin le left right = SourceEqualityConstraintConstructors.top := by
  obtain ⟨leftEmpty, leftAtoms⟩ := plain_fields left (SourceEqualityGuardReadback.active leftCached) leftPlain
  obtain ⟨rightEmpty, rightAtoms⟩ := plain_fields right (SourceEqualityGuardReadback.active rightCached) rightPlain
  simp only [SourceEqualityConstraintConstructors.conjoin, leftEmpty, rightEmpty, combineEqualities,
    GuardConjunction.merge, GuardConjunction.normalize, GuardConjunction.atoms, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, leftAtoms, rightAtoms, List.nil_append, GuardConjunction.canonical,
    List.eraseDups_nil, List.mergeSort_nil, GuardConjunction.conjoin, SourceEqualityConstraintConstructors.top]

/-- Two actual current field loads construct their own ready branch and plain result. -/
theorem current_loads_ready [DecidableEq (SourceGuards.Guard FullSyntax.Formula)]
    (le : SourceGuards.Guard FullSyntax.Formula → SourceGuards.Guard FullSyntax.Formula → Bool)
    (left right : Guard) (first second : Allocated) (arity : Nat) (before : Operations)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before)
    (leftCached : SourceEqualityGuardReadback.Cached left.equalities)
    (rightCached : SourceEqualityGuardReadback.Cached right.equalities)
    (leftLoad : SourceEqualityConstraintFieldLookup.load left before.constraints = .ok (some first))
    (rightLoad : SourceEqualityConstraintFieldLookup.load right before.constraints = .ok (some second))
    (leftPlain : SourceMemoGate.plain left = true) (rightPlain : SourceMemoGate.plain right = true) :
    ∃ result,
      (SourceEqualityIntersectionEdgeAllocation.run le first second arity arity before).1 = .ok (.ready result) ∧
      SourceEqualityConstraintMemoAllocation.Valid (SourceEqualityIntersectionEdgeAllocation.run le first second arity arity before).2 ∧
      SourceEqualityConstraintMemoAllocation.Grows before (SourceEqualityIntersectionEdgeAllocation.run le first second arity arity before).2 ∧
      Ready (SourceEqualityIntersectionEdgeAllocation.run le first second arity arity before).2.constraints result.stored ∧
      SourceMemoGate.plain (SourceEqualityConjoinAllocation.readback result) = true := by
  obtain ⟨firstReady, firstReadback⟩ := SourceEqualityConstraintFieldLookup.load_ready left before.constraints valid.constraints leftCached first leftLoad
  obtain ⟨secondReady, secondReadback⟩ := SourceEqualityConstraintFieldLookup.load_ready right before.constraints valid.constraints rightCached second rightLoad
  obtain ⟨branch, done, source, afterValid, grows, resultReady⟩ :=
    SourceEqualityIntersectionEdgeAllocation.run_correct le first second arity arity before valid firstReady secondReady
  have actualSource : SourceEqualityIntersectionEdgeAllocation.source le left right arity arity =
      .ready SourceEqualityConstraintConstructors.top := by
    simp [SourceEqualityIntersectionEdgeAllocation.source, conjoin_top le left right leftCached rightCached leftPlain rightPlain,
      SourceEqualityMkEdgeAllocation.accepted, SourceEqualityMkEdgeAllocation.contradictory,
      SourceEqualityMkEdgeAllocation.fits, SourceEqualityMkEdgeAllocation.signed,
      SourceEqualityConstraintConstructors.top, sourceEqualities, positiveNormalized, SymbolicSignedPaths.fitsArity]
  rw [firstReadback, secondReadback, actualSource] at source
  cases branch with
  | mismatch => cases source
  | rejected => cases source
  | ready result =>
      exact ⟨result, done, afterValid, grows, (resultReady result rfl).1,
        loaded_ready_plain le left right first second arity arity before valid leftCached rightCached
          leftLoad rightLoad leftPlain rightPlain result done⟩

/-- Initial plain fields construct two serial conjunctions in the actual returned operation states. -/
theorem construct_then_two_conjoins [DecidableEq (SourceGuards.Guard FullSyntax.Formula)]
    (le : SourceGuards.Guard FullSyntax.Formula → SourceGuards.Guard FullSyntax.Formula → Bool)
    (left right : Guard) (before : Operations) (valid : SourceEqualityConstraintMemoAllocation.Valid before)
    (leftCached : SourceEqualityGuardReadback.Cached left.equalities)
    (rightCached : SourceEqualityGuardReadback.Cached right.equalities)
    (leftPlain : SourceMemoGate.plain left = true) (rightPlain : SourceMemoGate.plain right = true) :
    ∃ first middle second loaded combined result,
      SourceEqualityConjoinAllocation.construct left.equalities left.guard before = (.ok first, middle) ∧
      SourceEqualityConjoinAllocation.construct right.equalities right.guard middle = (.ok second, loaded) ∧
      (SourceEqualityConjoinAllocation.conjoin le first second loaded).1 = .ok combined ∧
      (SourceEqualityConjoinAllocation.conjoin le combined second
        (SourceEqualityConjoinAllocation.conjoin le first second loaded).2).1 = .ok result ∧
      SourceMemoGate.plain (SourceEqualityConjoinAllocation.readback combined) = true ∧
      SourceMemoGate.plain (SourceEqualityConjoinAllocation.readback result) = true ∧
      SourceEqualityConstraintMemoAllocation.Valid
        (SourceEqualityConjoinAllocation.conjoin le combined second
          (SourceEqualityConjoinAllocation.conjoin le first second loaded).2).2 := by
  obtain ⟨first, middle, firstDone, middleValid, firstReady, firstReadback, _, _, _⟩ :=
    SourceEqualityConjoinAllocation.construct_complete left.equalities leftCached left.guard before valid
  obtain ⟨second, loaded, secondDone, loadedValid, secondReady, secondReadback, _, _, loadedGrowth⟩ :=
    SourceEqualityConjoinAllocation.construct_complete right.equalities rightCached right.guard middle middleValid
  have firstReady := firstReady.grows loadedGrowth.constraint_growth
  have firstPlain : SourceMemoGate.plain (SourceEqualityConjoinAllocation.readback first) = true := by
    rw [firstReadback]; exact leftPlain
  have secondPlain : SourceMemoGate.plain (SourceEqualityConjoinAllocation.readback second) = true := by
    rw [secondReadback]; exact rightPlain
  obtain ⟨combined, combinedDone, combinedValid, combinedReady, _, _, _, combinedGrowth⟩ :=
    SourceEqualityConjoinAllocation.conjoin_correct le first second loaded loadedValid firstReady secondReady
  have combinedPlain := conjoin_result_plain le first second loaded loadedValid firstReady secondReady
    firstPlain secondPlain combined combinedDone
  have nextSecondReady := secondReady.grows combinedGrowth.constraint_growth
  obtain ⟨result, resultDone, resultValid, _, _, _, _, _⟩ :=
    SourceEqualityConjoinAllocation.conjoin_correct le combined second
      (SourceEqualityConjoinAllocation.conjoin le first second loaded).2 combinedValid combinedReady nextSecondReady
  have resultPlain := conjoin_result_plain le combined second
    (SourceEqualityConjoinAllocation.conjoin le first second loaded).2 combinedValid combinedReady nextSecondReady
      combinedPlain secondPlain result resultDone
  exact ⟨first, middle, second, loaded, combined, result, firstDone, secondDone, combinedDone, resultDone,
    combinedPlain, resultPlain, resultValid⟩

/-- A literal mismatched body allocates only its sentinel field and emits its plain guard. -/
theorem sentinel_without_load (request : SourceRecursiveIntersectionKernel.EdgeRequest Symbol Guard)
    (before : SourceEqualityNativeDemand.State width)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before.operations)
    (mismatch : request.left.children.length ≠ request.right.children.length) :
    SourceEqualityNativeDemand.body request .pure before = SourceEqualityNativeDemand.sentinel request .pure before ∧
      SourceEqualityConstraintMemoAllocation.Valid (SourceEqualityMkEdgeAllocation.emptyField before.operations) ∧
      SourceEqualityConstraintMemoAllocation.Grows before.operations (SourceEqualityMkEdgeAllocation.emptyField before.operations) ∧
      SourceMemoGate.plain (SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)) = true := by
  have allocated := SourceEqualityMkEdgeAllocation.emptyField_correct before.operations valid
  exact ⟨SourceEqualityNativeDemand.body_mismatch request .pure before mismatch, allocated.1, allocated.2.1, top_plain⟩

#print axioms current_loads_ready
#check @current_loads_ready
#print axioms construct_then_two_conjoins
#check @construct_then_two_conjoins
#print axioms sentinel_without_load
#check @sentinel_without_load
end MicroCFTA.PlainGuardIndependent
