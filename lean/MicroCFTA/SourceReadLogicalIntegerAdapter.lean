import MicroCFTA.SourceReadLogicalGuards
import MicroCFTA.SolverAdapter
import MicroCFTA.CurrentReadLogicalPrune

/-!
# Integer declaration domains in the actual pure solver adapter

All ambient, fresh, and default declarations remain Int. Every value in an
integer carrier therefore meets the prepared declaration domain. A returned
adapter verdict supplies the soundness premise for planned-read transport.
Ambient-name collisions retain their actual Unknown result. Exceptions stay
outside the returned-callback premise, and no name-stability is assumed.
-/
namespace MicroCFTA.SourceReadLogicalIntegerAdapter
open FullSyntax SourceFormula SourceObservations
open SolverAdapter
open SourceGuards (Guard Observations)

/-- Every declaration in this fragment uses the source Int sort. -/
def IntegerDeclarations (declared : List Declaration) : Prop := ∀ binding ∈ declared, binding.2 = .int

/-- The source default value declaration retains an all-Int ambient context. -/
theorem declarations_integer (given : List Declaration) (integer : IntegerDeclarations given) :
    IntegerDeclarations (declarations given) := by
  unfold declarations
  split
  · exact integer
  · intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · rfl
    · exact integer binding member

/-- First-match ambient lookup and its default both return Int in the integer fragment. -/
theorem lookup_integer (ambient : List Declaration) (integer : IntegerDeclarations ambient) (name : Name) :
    (lookupSort name ambient).getD .int = .int := by
  induction ambient with
  | nil => rfl
  | cons binding rest ih =>
      have head := integer binding (by simp)
      have tail := ih (fun binding member => integer binding (by simp [member]))
      rcases binding with ⟨key, sort⟩
      simp only [lookupSort]
      split <;> simp_all

/-- Every successfully generated fresh declaration retains Int. -/
theorem fresh_integer (ambient : List Declaration) (integer : IntegerDeclarations ambient)
    (bindings : List (Name × Name)) (fresh : List Declaration)
    (found : freshDeclarations ambient bindings = some fresh) : IntegerDeclarations fresh := by
  induction bindings generalizing fresh with
  | nil => simp [freshDeclarations] at found; subst fresh; simp [IntegerDeclarations]
  | cons binding rest ih =>
      cases first : freshDeclaration ambient binding with
      | none => simp [freshDeclarations, first] at found
      | some declaration =>
          cases later : freshDeclarations ambient rest with
          | none => simp [freshDeclarations, first, later] at found
          | some tail =>
              simp [freshDeclarations, first, later] at found
              subst fresh
              have declared : declaration.2 = .int := by
                unfold freshDeclaration at first
                split at first
                · contradiction
                · have equal := Option.some.inj first
                  rw [← equal]
                  exact lookup_integer ambient integer binding.2
              intro entry member
              rcases List.mem_cons.mp member with rfl | member
              · exact declared
              · exact ih tail later entry member

/-- Successful full preflight preserves the all-Int domain, including default free-name declarations. -/
theorem prepared_integer (given : List Declaration) (integer : IntegerDeclarations given)
    (bindings : List (Name × Name)) (assumptions : List Formula) (antecedent consequent : Formula)
    (request : Prepared) (found : prepareQuery given bindings assumptions antecedent consequent = some request) :
    IntegerDeclarations request.declared := by
  cases fresh : freshDeclarations (declarations given) bindings with
  | none => simp [prepareQuery, prepare, fresh] at found
  | some entries =>
      simp [prepareQuery, prepare, fresh] at found
      subst request
      have ambient := declarations_integer given integer
      have generated := fresh_integer (declarations given) ambient bindings entries fresh
      intro binding member
      simp only [List.mem_append] at member
      rcases member with old | (new | added)
      · exact ambient binding old
      · exact generated binding new
      · obtain ⟨name, _, equal⟩ := List.mem_map.mp added
        exact congrArg Prod.snd equal.symm

/-- All integer values meet the exact prepared declaration domain. -/
theorem admitted_integer (model : FormulaLowering.Model Value) (allInteger : ∀ value, model.hasSort .int value)
    (declared : List Declaration) (integer : IntegerDeclarations declared) (env : Name → Value) : Admitted model declared env := by
  intro binding member
  rw [integer binding member]
  exact allInteger (env binding.1)

/-- Each returned actual adapter verdict is sound for the unrestricted integer carrier. -/
theorem returned_supports (model : FormulaLowering.Model Value) (allInteger : ∀ value, model.hasSort .int value)
    (given : List Declaration) (integer : IntegerDeclarations given) (bindings : List (Name × Name))
    (antecedent consequent : Formula) (milliseconds : Int) (check : Prepared → Attempt)
    (correct : ∀ request response reached, check request = .answered response reached → ResponseCorrect model request response)
    (verdict : Guards.Verdict)
    (returned : (execute given bindings [] antecedent consequent milliseconds check).result = .returned verdict) :
    Guards.Supports verdict (SourceEntailment.Entails (FormulaLowering.sourceModel model) (fun _ => True) antecedent consequent) := by
  cases found : prepareQuery given bindings [] antecedent consequent with
  | none =>
      have unknown : verdict = .unknown := by simpa [execute, found] using returned.symm
      subst verdict
      trivial
  | some request =>
      have sound := execute_sound model given bindings [] antecedent consequent milliseconds check request found (correct request)
      rw [returned] at sound
      have domain := prepared_integer given integer bindings [] antecedent consequent request found
      cases verdict with
      | unknown => trivial
      | yes => exact fun env _ assumed => sound env (admitted_integer model allInteger request.declared domain env) (by simp [FullSyntax.holdsAll]) assumed
      | no => exact fun proved => sound (fun env _ _ assumed => proved env trivial assumed)

/-- A returned callback agrees with the real adapter, including preflight Unknown. -/
def Returned (given : List Declaration) (milliseconds : Int) (check : Prepared → Attempt)
    (solver : SourceGuards.Entailment Formula) : Prop :=
  ∀ bindings antecedent consequent,
    (execute given bindings [] antecedent consequent milliseconds check).result = .returned (solver bindings antecedent consequent)

/-- Correct external responses give the sound callback needed by guard transport. -/
theorem callback_sound (model : FormulaLowering.Model Value) (allInteger : ∀ value, model.hasSort .int value)
    (given : List Declaration) (integer : IntegerDeclarations given) (milliseconds : Int) (check : Prepared → Attempt)
    (correct : ∀ request response reached, check request = .answered response reached → ResponseCorrect model request response)
    (solver : SourceGuards.Entailment Formula) (returned : Returned given milliseconds check solver) :
    SourceEntailment.Sound (FormulaLowering.sourceModel model) (fun _ _ => True) solver := by
  intro bindings antecedent consequent
  exact returned_supports model allInteger given integer bindings antecedent consequent milliseconds check correct _
    (returned bindings antecedent consequent)

/-- The actual all-Int adapter supplies planned-read logical evidence without spelling-stability assumptions. -/
theorem guard_supports (model : FormulaLowering.Model Value) (allInteger : ∀ value, model.hasSort .int value)
    (laws : FormulaSimplify.RelationLaws (FormulaLowering.sourceModel model))
    (given : List Declaration) (integer : IntegerDeclarations given) (milliseconds : Int) (check : Prepared → Attempt)
    (correct : ∀ request response reached, check request = .answered response reached → ResponseCorrect model request response)
    (solver : SourceGuards.Entailment Formula) (returned : Returned given milliseconds check solver)
    (term : Language.Term (Label Formula)) (guard : Guard Formula) (cell : Observations Formula)
    (reads : SourceReadAgreement.Reads guard cell (observe term)) (positive : Bool) :
    Guards.Supports (SourceSubstitutionPrecedence.evaluate operations solver cell (sameShape operations cell) positive guard)
      (SourceQuotientGuards.Public (FormulaLowering.sourceModel model) (fun _ _ => True) term positive guard) := by
  have sound := callback_sound model allInteger given integer milliseconds check correct solver returned
  apply SourceReadLogicalGuards.public_supports (FormulaLowering.sourceModel model) (by intro value; rfl) laws
    (fun _ _ => True) solver term guard cell reads (fun _ _ => ⟨fun _ _ _ _ => trivial, fun _ _ _ _ => trivial⟩)
  intro context member declarations antecedent consequent
  have support := sound declarations antecedent consequent
  cases result : solver declarations antecedent consequent with
  | unknown => trivial
  | yes =>
      rw [result] at support
      exact fun env _ assumed => support env trivial assumed
  | no =>
      rw [result] at support
      exact fun proved => support (fun env _ assumed => proved env ⟨fun _ _ => trivial, fun _ _ => trivial⟩ assumed)

/-- An unused ambient integer declaration still forces Unknown at an actual generated-name collision. -/
theorem collision_unknown (check : Prepared → Attempt) :
    execute [("__cfta_actual_0", .int)] [("__cfta_actual_0", "a")] [] .top .top 10000 check =
      ⟨false, .returned .unknown⟩ := by
  apply rejected_without_check
  decide +kernel

/-- A successful current prune under returned all-Int adapter calls contains only logical-valid original terms. -/
theorem prune_sound (model : FormulaLowering.Model Value) (allInteger : ∀ value, model.hasSort .int value)
    (laws : FormulaSimplify.RelationLaws (FormulaLowering.sourceModel model))
    (given : List Declaration) (integer : IntegerDeclarations given) (milliseconds : Int) (check : Prepared → Attempt)
    (correct : ∀ request response reached, check request = .answered response reached → ResponseCorrect model request response)
    (solver : SourceGuards.Entailment Formula) (returned : Returned given milliseconds check solver)
    (automaton : Language.Automaton State (Observation.Label String Formula)) (guard : Guard Formula) (state : State)
    (result : List (ObservationGraph.Node State (Observation.Label String Formula)))
    (success : CurrentGuardPrune.prune operations solver automaton guard state = .ok result)
    (term : Language.Term (Observation.Label String Formula))
    (retained : PruneCandidates.Denotes (ObservationGraph.AcceptsNode automaton) result term) :
    Language.Accepts automaton state term ∧ CurrentReadLogicalPrune.Logical (FormulaLowering.sourceModel model) (FullGuardPrune.sourceTerm term) guard :=
  CurrentReadLogicalPrune.prune_sound (FormulaLowering.sourceModel model) (by intro value; rfl) laws solver
    (callback_sound model allInteger given integer milliseconds check correct solver returned)
    automaton guard state result success term retained

/-- Successful current pruning retains every term confirmed by the complete returned adapter. -/
theorem confirmed_retained (model : FormulaLowering.Model Value) (allInteger : ∀ value, model.hasSort .int value)
    (laws : FormulaSimplify.RelationLaws (FormulaLowering.sourceModel model))
    (given : List Declaration) (integer : IntegerDeclarations given) (milliseconds : Int) (check : Prepared → Attempt)
    (correct : ∀ request response reached, check request = .answered response reached → ResponseCorrect model request response)
    (solver : SourceGuards.Entailment Formula) (returned : Returned given milliseconds check solver)
    (automaton : Language.Automaton State (Observation.Label String Formula)) (guard : Guard Formula) (state : State)
    (result : List (ObservationGraph.Node State (Observation.Label String Formula)))
    (success : CurrentGuardPrune.prune operations solver automaton guard state = .ok result)
    (term : Language.Term (Observation.Label String Formula)) (accepted : Language.Accepts automaton state term)
    (yes : SourceSubstitutionPrecedence.evaluateGuard operations solver guard (FullGuardPrune.sourceTerm term) = .yes) :
    PruneCandidates.Denotes (ObservationGraph.AcceptsNode automaton) result term :=
  CurrentReadLogicalPrune.confirmed_retained (FormulaLowering.sourceModel model) (by intro value; rfl) laws solver
    (callback_sound model allInteger given integer milliseconds check correct solver returned)
    automaton guard state result success term accepted yes

/-- Returned all-Int adapter decisions give exact logical compiler classification on successful cells. -/
theorem compile_exact (model : FormulaLowering.Model Value) (allInteger : ∀ value, model.hasSort .int value)
    (laws : FormulaSimplify.RelationLaws (FormulaLowering.sourceModel model))
    (given : List Declaration) (integer : IntegerDeclarations given) (milliseconds : Int) (check : Prepared → Attempt)
    (correct : ∀ request response reached, check request = .answered response reached → ResponseCorrect model request response)
    (solver : SourceGuards.Entailment Formula) (returned : Returned given milliseconds check solver)
    (guard : Guard Formula) (cell : Observations Formula) (term : Language.Term (Label Formula))
    (reads : SourceReadAgreement.Reads guard cell (observe term))
    (semantic allYes allNo : Guards.Verdict) (mixedLeaf equalities same answer : Bool)
    (success : BooleanGuardCompile.decision solver guard cell semantic allYes allNo mixedLeaf equalities same = .ok answer) :
    answer = true ↔ CurrentReadLogicalPrune.Logical (FormulaLowering.sourceModel model) term guard :=
  CurrentReadLogicalPrune.compile_exact (FormulaLowering.sourceModel model) (by intro value; rfl) laws solver
    (callback_sound model allInteger given integer milliseconds check correct solver returned)
    guard cell term reads semantic allYes allNo mixedLeaf equalities same answer success

end MicroCFTA.SourceReadLogicalIntegerAdapter
