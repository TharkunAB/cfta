import MicroCFTA.SourceSynthesisNormalizedVariablePaths
import MicroCFTA.SourceEqualityInheritedGrowthBoundary
import MicroCFTA.SourceSynthesisOriginalGuardAlphabet
import MicroCFTA.SourceConstraintEntryRaw

/-!
# Prefix freedom can fail between original Type guards

Each guard comes from a finite original library Type. The source normalizer
and source conjunction compute the combined field. This is a constructor
boundary. It does not assert that a native query reaches this conjunction,
that a caller repeats a walk, or that an execution does not terminate.
-/
namespace MicroCFTA.SourceSynthesisTypeConjunctionBoundary
open SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax (Guard top eqGuard equalityClasses)
open SourceSynthesisFirstOrderConstruction
open SourceSynthesisInitialTypeFields (Program ProgramRow)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option cbv.maxSteps 200000000

private theorem array_small (classes : EqualityNormalize.Constraints) :
    SourceCompactGuards.arrayNormalize classes = SourceEqualityNormalizationReceipt.observed 16 classes :=
  SourceEqualityNormalizationReceipt.observed_eq 16 classes

attribute [local cbv_eval] array_small SourceSynthesisGeneralizeSyntax.eqGuard_eq_source

/-- The first variable occurs at paths zero and one-zero-zero. -/
def firstType : Ty :=
  .tCons "Root" [.tVar "a", .tCons "Unary" [.tCons "Pair" [.tVar "a", .tCons "Fill0" []]]]

/-- The second variable occurs at paths zero-one and one-zero-one. -/
def secondType : Ty :=
  .tCons "Root" [.tCons "Pair" [.tCons "Fill1" [], .tVar "b"],
    .tCons "Unary" [.tCons "Pair" [.tVar "c", .tVar "b"]]]

/-- The first complete guard is the actual generalization field. -/
def firstGuard : Guard := eqGuard (equalityClasses firstType)

/-- The second complete guard is the actual generalization field. -/
def secondGuard : Guard := eqGuard (equalityClasses secondType)

/-- The combined guard uses the actual source constraint conjunction. -/
noncomputable def joinedGuard : Guard := conjoin firstGuard secondGuard

/-- Prefix freedom concerns all endpoints of the stored normalized field. -/
def PrefixFree (guard : Guard) : Prop :=
  ∀ first ∈ EqualityNormalize.members (guard.equalities.getD []),
    ∀ second ∈ EqualityNormalize.members (guard.equalities.getD []),
      first.IsPrefix second → first = second

/-- This source library contains both original Types without any name restriction. -/
def library : Library :=
  { libraryGroups := [("first", firstType, []), ("second", secondType, [])]
    libraryArgumentOnly := []
    libraryAvoid := []
    libraryEncoding := .firstOrder }

/-- The rigid goal adds only Top guards. -/
def query : Query := { queryArguments := [], queryGoal := .tCons "Goal" [] }

/-- The first source class is computed from actual recognized variable occurrences. -/
theorem first_classes : equalityClasses firstType = [[[0], [1, 0, 0]]] := by cbv

/-- The other Type adds a repeated class and one fresh singleton class. -/
theorem second_classes : equalityClasses secondType = [[[0, 1], [1, 0, 1]], [[1, 0, 0]]] := by cbv

/-- Every normalized endpoint of the first original field is prefix-free. -/
theorem first_prefix_free : PrefixFree firstGuard := by
  intro first firstMember second secondMember pfx
  exact SourceSynthesisNormalizedVariablePaths.eqGuard_prefix_free firstType first second firstMember secondMember pfx

/-- Every normalized endpoint of the second original field is prefix-free. -/
theorem second_prefix_free : PrefixFree secondGuard := by
  intro first firstMember second secondMember pfx
  exact SourceSynthesisNormalizedVariablePaths.eqGuard_prefix_free secondType first second firstMember secondMember pfx

/-- Actual source conjunction produces the previously normalized two-class field. -/
theorem conjunction_eq_fixture : joinedGuard = SourceEqualityInheritedGrowthBoundary.localConstraint := by
  cbv

private theorem shorter_member :
    [1, 0, 0] ∈ EqualityNormalize.members (joinedGuard.equalities.getD []) := by
  cbv
  exact .tail _ (.head _)

private theorem longer_member :
    [1, 0, 0, 1] ∈ EqualityNormalize.members (joinedGuard.equalities.getD []) := by
  cbv
  exact .tail _ (.tail _ (.tail _ (.head _)))

/-- Global prefix freedom of one generalized Type does not survive source conjunction. -/
theorem conjunction_not_prefix_free : ¬ PrefixFree joinedGuard := by
  intro free
  have same := free [1, 0, 0] shorter_member [1, 0, 0, 1] longer_member ⟨[1], rfl⟩
  cases same

/-- Each original stored field has maximum endpoint length three. -/
theorem original_maxima :
    (SourceEqualityInheritedGrowthBoundary.pathLength (firstGuard.equalities.getD []),
      SourceEqualityInheritedGrowthBoundary.pathLength (secondGuard.equalities.getD [])) = (3, 3) := by
  cbv

/-- One actual source conjunction increases the maximum stored endpoint length to four. -/
theorem conjunction_maximum :
    SourceEqualityInheritedGrowthBoundary.pathLength (joinedGuard.equalities.getD []) = 4 := by
  cbv

/-- This finite term has compatible constructor shapes for both original Type patterns. -/
def commonTerm : Language.Term (SourceObservations.Label FullSyntax.Formula) :=
  .node ("Root", .top)
    [.node ("Pair", .top) [.node ("Fill1", .top) [], .node ("Fill0", .top) []],
     .node ("Unary", .top)
       [.node ("Pair", .top)
         [.node ("Pair", .top) [.node ("Fill1", .top) [], .node ("Fill0", .top) []],
          .node ("Fill0", .top) []]]]

/-- The same existing subterms satisfy both actual normalized fields and their conjunction. -/
theorem common_satisfies :
    SourceEqualityGuardReadback.Sat commonTerm firstGuard.equalities ∧
    SourceEqualityGuardReadback.Sat commonTerm secondGuard.equalities ∧
    SourceEqualityGuardReadback.Sat commonTerm joinedGuard.equalities := by
  have firstStored : firstGuard.equalities = some [[[0], [1, 0, 0]]] := by cbv
  have secondStored : secondGuard.equalities = some [[[0, 1], [1, 0, 1]]] := by cbv
  have joinedStored : joinedGuard.equalities =
      some [[[0], [1, 0, 0]], [[0, 1], [1, 0, 0, 1], [1, 0, 1]]] := by cbv
  simp [firstStored, secondStored, joinedStored, SourceEqualityGuardReadback.Sat,
    EqualityNormalize.Satisfies, EqualityNormalize.ClassSat, Language.PathsEqual,
    commonTerm, Language.Term.atPath]

/-- The current complete constraint evaluator accepts that finite term. -/
theorem common_accepted (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    SourceConstraintEntryRaw.acceptsConstraint formulas solver joinedGuard commonTerm = true := by
  have active : SourceCompactGuards.ActiveOption joinedGuard.equalities := by
    rw [conjunction_eq_fixture]
    exact SourceCompactGuards.normalize_active SourceEqualityInheritedGrowthBoundary.raw
  have residual : joinedGuard.guard = .top := by rw [conjunction_eq_fixture]; rfl
  rw [SourceConstraintEntryRaw.accepts_of_active formulas solver joinedGuard active commonTerm]
  change (ConstraintIndicators.equalityValue (SymbolicDriver.classTest commonTerm) joinedGuard.equalities &&
    decide (SourceBooleanEntry.evaluateGuard formulas solver joinedGuard.guard commonTerm = .yes)) = true
  apply Bool.and_eq_true_iff.mpr
  constructor
  · exact (SourceEqualityGuardReadback.value_exact commonTerm joinedGuard.equalities active).mpr common_satisfies.2.2
  · rw [residual]
    simp only [decide_eq_true_eq]
    simp [SourceBooleanEntry.evaluateGuard, SourceBooleanEntry.evaluateGuardWithSame,
      SourceBooleanEntry.evaluate, SourceBooleanEntry.evaluateScoped, SourceBooleanEntry.signed,
      SourceGuards.evaluateGuardWithSame, SourceGuards.evaluateWith, SourceGuards.polarize]

/-- Both generalized fields occur in the exact original component instruction variants. -/
theorem original_fields :
    ProgramRow library query (component (typesOf library query) "first" firstType) ∧
    ProgramRow library query (component (typesOf library query) "second" secondType) := by
  exact ⟨ProgramRow.component ("first", firstType, []) List.mem_cons_self,
    ProgramRow.component ("second", secondType, []) (List.mem_cons_of_mem _ List.mem_cons_self)⟩

/-- A size-one source request is accepted and derives its initial source-field certificate. -/
theorem accepted_fields :
    ∃ expression, firstOrderRaw library query 1 = .ok expression ∧ Program library query expression := by
  have succeeds : (match firstOrderRaw library query 1 with | .error _ => false | .ok _ => true) = true := by
    cbv
  cases actual : firstOrderRaw library query 1 with
  | error failure => simp_all
  | ok expression =>
      exact ⟨expression, rfl,
        SourceSynthesisInitialTypeFields.firstOrderRaw_fields library query 1 expression actual⟩

/-- The counterexample already belongs to conjunction closure of the actual original alphabet. -/
theorem original_conjunction :
    SourceEqualityConstraintOrigins.Derived (SourceSynthesisOriginalGuardAlphabet.alphabet library)
      top conjoin joinedGuard := by
  apply SourceEqualityConstraintOrigins.Derived.conjunction
  · apply SourceEqualityConstraintOrigins.Derived.literal
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_append_left _ (List.mem_map.mpr ⟨("first", firstType, []), List.mem_cons_self, rfl⟩))))
  · apply SourceEqualityConstraintOrigins.Derived.literal
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_append_left _ (List.mem_map.mpr
        ⟨("second", secondType, []), List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩))))

end MicroCFTA.SourceSynthesisTypeConjunctionBoundary
