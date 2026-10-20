import MicroCFTA.SourceCurrentNativeOptionalPrefix
import MicroCFTA.SourceCurrentAllocatedNativeMuSource

/-!
# Exact child and own optional sites in a Mu compiler prefix

The first actual instruction enters the captured body's child domain.
The remaining prefix either reaches a child optional instruction or the
compiler's own optional instruction at the exact child return state.
-/
namespace MicroCFTA.SourceCurrentNativeMuOptionalPrefix
open InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceRecursiveIntersectionKernel
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentNativeOptionalPrefix (bound_optional_cases)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Inputs" => SourceCurrentAllocatedNativePhysicalExecution.Inputs
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem own_optional (fuel : Nat) (own selected : Nat × Nat)
    (value siteBody : Value Symbol Guard) (siteNext : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard))
    (before after : Checked width)
    (actual : Trace fuel (.code (.optionalBinder own value .pure)) before
      (.code (.optionalBinder selected siteBody siteNext)) after) :
    fuel = 0 ∧ selected = own ∧ siteBody = value ∧ siteNext = .pure ∧ after = before := by
  cases actual with
  | refl => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | cons start initial next middle final result count inputs one tail =>
      cases called : SourceRecursiveIntersectionMaybeMu.maybeMu own value before.native.machine.heap with
      | pending key heap =>
          simp only [step, SourceRecursiveIntersectionNative.step, called, lift] at one
          cases one
      | done output heap =>
          simp only [step, SourceRecursiveIntersectionNative.step, called, lift] at one
          cases one
          cases tail with
          | cons _ _ _ _ _ _ _ _ one _ => cases one

/-- An actual unbound Mu prefix retains its entered child site or exact own optional site. -/
theorem trace (request : NodeRequest Symbol Guard) (fuel : Nat) (before siteBefore : Checked width)
    (selectedPair : Nat × Nat) (siteBody : Value Symbol Guard)
    (siteNext : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard))
    (actual : Trace fuel (.code (compileMu request.domain request.left request.right)) before
      (.code (.optionalBinder selectedPair siteBody siteNext)) siteBefore) :
    ∃ first second count,
      let entered := SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains request.domain.key
        request.left request.right first second
      let childBefore := {before with native := advance before.native {before.native.machine with domains := entered.2}}
      SourceRecursiveIntersectionControl.identity request.left = some first ∧
      SourceRecursiveIntersectionControl.identity request.right = some second ∧
      fuel = count + 1 ∧ Inputs (.code (compileMu request.domain request.left request.right)) before ∧
      step (.code (compileMu request.domain request.left request.right)) before =
        .yielded (.code (.node ⟨entered.1, body request.left, body request.right⟩
          (fun value => .optionalBinder (SourceRecursiveIntersectionControl.pair first second) value .pure))) childBefore ∧
      ((∃ innerNext,
          Trace count (.code (requestNode entered.1 (body request.left) (body request.right))) childBefore
            (.code (.optionalBinder selectedPair siteBody innerNext)) siteBefore ∧
          siteNext = fun value => (innerNext value).bind
            (fun body => .optionalBinder (SourceRecursiveIntersectionControl.pair first second) body .pure)) ∨
        (selectedPair = SourceRecursiveIntersectionControl.pair first second ∧ siteNext = .pure ∧
          Trace count (.code (requestNode entered.1 (body request.left) (body request.right))) childBefore
            (.code (.pure siteBody)) siteBefore)) := by
  cases first : SourceRecursiveIntersectionControl.identity request.left with
  | none =>
      simp only [compileMu, first, SourceRecursiveIntersectionCode.unsupported] at actual
      cases actual with
      | cons _ _ _ _ _ _ _ _ one _ => cases one
  | some firstValue =>
    cases second : SourceRecursiveIntersectionControl.identity request.right with
    | none =>
        simp only [compileMu, first, second, SourceRecursiveIntersectionCode.unsupported] at actual
        cases actual with
        | cons _ _ _ _ _ _ _ _ one _ => cases one
    | some secondValue =>
        let entered := SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains request.domain.key
          request.left request.right firstValue secondValue
        let childBefore := {before with native := advance before.native {before.native.machine with domains := entered.2}}
        have one := SourceCurrentAllocatedNativeMuSource.enter_prefix request before firstValue secondValue first second
        have exposed : compileMu request.domain request.left request.right =
            .enter request.domain request.left request.right firstValue secondValue (fun entered =>
              .node ⟨entered, body request.left, body request.right⟩ (fun value =>
                .optionalBinder (SourceRecursiveIntersectionControl.pair firstValue secondValue) value .pure)) := by
          simp only [compileMu, first, second]
        rw [exposed] at actual
        cases actual with
        | cons start initial next middle final result count inputs actualStep tail =>
            have enteredStep := one
            rw [exposed] at enteredStep
            obtain ⟨same, retained⟩ := Outcome.yielded.inj (enteredStep.symm.trans actualStep)
            subst next
            subst middle
            refine ⟨firstValue, secondValue, count, first, second, rfl, ?_, one, ?_⟩
            · simpa only [exposed] using inputs
            · rcases bound_optional_cases count
                  (.code (requestNode entered.1 (body request.left) (body request.right)))
                  (fun body => .optionalBinder (SourceRecursiveIntersectionControl.pair firstValue secondValue) body .pure)
                  childBefore siteBefore selectedPair siteBody siteNext tail with unfinished | completed
              · exact Or.inl unfinished
              · obtain ⟨innerFuel, outerFuel, value, middle, total, called, later⟩ := completed
                obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := own_optional outerFuel
                  (SourceRecursiveIntersectionControl.pair firstValue secondValue) selectedPair value siteBody siteNext
                  middle siteBefore later
                have same : innerFuel = count := by omega
                subst innerFuel
                exact Or.inr ⟨rfl, rfl, called⟩

end MicroCFTA.SourceCurrentNativeMuOptionalPrefix
