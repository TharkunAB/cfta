import MicroCFTA.InternedGuardedBudgetValueRefinement
import MicroCFTA.InternedGuardedBudgetStoredExecution
import MicroCFTA.InternedGuardedBudgetStoredPlan

/-!
# Actual stored reconstruction retains and lowers unfolding budgets

The exact raw compiler and smart executor compose through the proved plan
inclusion. Simultaneous substitution retains each accepted raw budget.
Actual outer-Mu unfolding accepts the same term at a strictly smaller bound.
-/
namespace MicroCFTA.InternedGuardedBudgetStoredRefinement
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedStoredSubstitution (Environment Replacements leaves input encode)
open InternedFreshOrdinaryContext InternedGuardedBudget InternedGuardedBudgetProbeHeap InternedGuardedBudgetRequest
open InternedBinderProtocol (Reference NodeKey)
open BinderBudgetLanguage (Included Upward)

/-- Actual simultaneous stored substitution retains every accepted replacement budget and both probe heaps. -/
theorem execute_refines [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (replacements : Environment Symbol Guard) (state : State Symbol Guard) (context : Context state [])
    (heap : Heap state) (depthHeap : InternedFreshOrdinaryDepthHeap.Heap state)
    (available : Available state value) (valid : Replacements state replacements) :
    Checked (InternedFreshOrdinaryStoredSubstitution.execute value replacements state) (fun result => ∀ holds ambient,
      (∀ name, Upward (ambient name)) → Included
        (meaning holds (InternedGuardedBudgetStoredPlan.replacementEnv holds ambient replacements) value)
        (meaning holds ambient result)) := by
  have executed := InternedGuardedBudgetStoredExecution.execute_checked value replacements state context heap depthHeap available valid
  refine ⟨executed.heap, executed.depthHeap, ?_⟩
  intro result after done holds ambient upward budget term accepted
  have raw := InternedGuardedBudgetStoredPlan.execute_plan_language holds ambient value replacements state context.normal.facts.coherent available
  rw [← raw] at accepted
  have compared := InternedGuardedBudgetPlanRefinement.values_refine holds ((leaves value).map (input replacements))
    (encode (leaves value) [] value) ambient upward
  have acceptedRaw : InternedGuardedBudgetSyntax.evaluate holds
      (((leaves value).map (input replacements)).map (meaning holds ambient)) (encode (leaves value) [] value) budget term := by
    simpa only [List.map_map, Function.comp_def] using accepted
  rw [executed.result result after done holds ambient]
  exact compared budget term acceptedRaw

/-- Every actual returned outer-Mu unfolding accepts each input term at a strictly smaller budget. -/
theorem unfold_strict [DecidableEq (EdgeKey Symbol Guard)] (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard) (state : State Symbol Guard) (context : Context state [])
    (heap : Heap state) (depthHeap : InternedFreshOrdinaryDepthHeap.Heap state)
    (available : Available state (.mu entry body depth ordinary)) (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary) state = .done result after)
    (holds : Guard → Term Symbol → Bool) (ambient : Env Symbol) (upward : ∀ name, Upward (ambient name))
    (budget : Nat) (term : Term Symbol) (accepted : meaning holds ambient (.mu entry body depth ordinary) budget term) :
    ∃ smaller, smaller < budget ∧ meaning holds ambient result smaller term := by
  have bodyAvailable := available.children body (by simp [InternedProbeProvenance.children])
  let replacements : Environment Symbol Guard := fun name =>
    if name = .interned entry.identity then some (.mu entry body depth ordinary) else none
  have valid : Replacements state replacements := by
    intro name replacement found
    dsimp only [replacements] at found
    split at found
    · cases found; exact available
    · contradiction
  have executed := execute_refines body replacements state context heap depthHeap bodyAvailable valid
  obtain ⟨smaller, less, before⟩ := InternedGuardedBudgetStoredPlan.unfold_plan_lower holds ambient entry body depth ordinary
    state context.normal.facts.coherent bodyAvailable budget term accepted
  refine ⟨smaller, less, ?_⟩
  apply executed.result result after done holds ambient upward smaller term
  rw [← InternedGuardedBudgetStoredPlan.execute_plan_language holds ambient body replacements state context.normal.facts.coherent bodyAvailable]
  exact before

/-- Empty-cache source construction derives every budget heap and input premise for strict actual unfolding. -/
theorem constructed_unfold_strict [DecidableEq (EdgeKey Symbol Guard)]
    (expression : InternedNestedConstruction.Syntax Symbol Guard) (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard) (state : State Symbol Guard)
    (constructed : InternedFreshOrdinaryConstruction.build expression [] empty = .done (.mu entry body depth ordinary) state)
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary) state = .done result after)
    (holds : Guard → Term Symbol → Bool) (ambient : Env Symbol) (upward : ∀ name, Upward (ambient name))
    (budget : Nat) (term : Term Symbol) (accepted : meaning holds ambient (.mu entry body depth ordinary) budget term) :
    ∃ smaller, smaller < budget ∧ meaning holds ambient result smaller term := by
  have built := InternedGuardedBudgetExecution.build_language expression [] empty empty_context empty_heap InternedFreshOrdinaryDepthHeap.empty_heap
  have context : Context state [] := by
    simpa only [constructed, InternedNestedConstruction.Outcome.state] using empty_context.build expression
  have heap : Heap state := by simpa only [constructed, InternedNestedConstruction.Outcome.state] using built.heap
  have depthHeap : InternedFreshOrdinaryDepthHeap.Heap state := by
    simpa only [constructed, InternedNestedConstruction.Outcome.state] using built.depthHeap
  have verified := InternedFreshOrdinaryFacts.build_verified expression [] empty InternedNestedFacts.empty_facts
    (by intro value member; cases member)
  exact unfold_strict entry body depth ordinary state context heap depthHeap
    (verified.result _ _ constructed) result after done holds ambient upward budget term accepted

end MicroCFTA.InternedGuardedBudgetStoredRefinement
