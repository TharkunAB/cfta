import MicroCFTA.InternedGuardedSmartBudgetValues
import MicroCFTA.InternedGuardedBudgetProbeHeap
import MicroCFTA.InternedRecordDepthExecution

/-!
# Budget observations of actual normalized callbacks

One symbolic body supplies both ordinary-probe readbacks. Actual filtering
retains the raw Mu and empty-local languages. Only surviving captures need
freshness. The existing callback shape theorem supplies the smart decision.
-/
namespace MicroCFTA.InternedGuardedBudgetCallback
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax)
open InternedNestedProvenance (Values)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts InternedFreshOrdinaryContext
open InternedGuardedBudget
open InternedBinderProtocol (Reference)
open BinderBudgetLanguage (Lang)

/-- The complete symbolic body reads one local language and the actual captured budget languages. -/
def bodyMeaning (holds : Guard → Term Symbol → Bool) (environment : Env Symbol)
    (expression : Syntax Symbol Guard) (values : List (Value Symbol Guard)) (candidate : Lang Symbol) : Lang Symbol :=
  InternedGuardedSmartBudget.evaluate holds
    (⟨[Sum.inl ()], [], false, 0⟩ :: (values.map InternedRecordDepthShape.shape).map (InternedDepthSemantics.Shape.map Sum.inr))
    (candidate :: values.map (meaning holds environment)) expression

/-- A callback retains the raw-Mu and empty-local observations of one symbolic body. -/
def View (holds : Guard → Term Symbol → Bool) (environment : Env Symbol) (name : Reference)
    (value : Value Symbol Guard) (expected : Lang Symbol → Lang Symbol) : Prop :=
  (BinderBudgetLanguage.mu (fun candidate => meaning holds (bind environment name candidate) value) = BinderBudgetLanguage.mu expected) ∧
    meaning holds (bind environment name (fun _ _ => False)) value = expected (fun _ _ => False)

/-- A normalized callback retains both raw-Mu and empty-local symbolic body languages. -/
theorem filter_view [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (values : List (Value Symbol Guard)) (name : Reference) (value : Value Symbol Guard)
    (state : State Symbol Guard) (context : Context state values) (available : Available state value)
    (observed : ∀ holds ambient, meaning holds ambient value =
      InternedGuardedSmartBudget.evaluate holds ((Value.reference name :: values).map InternedRecordDepthShape.shape)
        ((Value.reference name :: values).map (meaning holds ambient)) expression)
    (fresh : name ∉ InternedProfileCallbackForm.captures
      (InternedFreeNameForm.symbolic expression (values.map InternedRootProfile.profile) (values.map Value.free)))
    (holds : Guard → Term Symbol → Bool) (ambient : Env Symbol) :
    (BinderBudgetLanguage.mu (fun candidate => meaning holds (bind ambient name candidate)
        (run (withoutSelfReference name value) state).1) = BinderBudgetLanguage.mu (bodyMeaning holds ambient expression values)) ∧
      meaning holds (bind ambient name (fun _ _ => False)) (run (withoutSelfReference name value) state).1 =
        bodyMeaning holds ambient expression values (fun _ _ => False) := by
  have interpreted (candidate : Lang Symbol) :
      meaning holds (bind ambient name candidate) value = bodyMeaning holds ambient expression values candidate := by
    rw [observed, InternedGuardedSmartBudgetValues.body_supplied holds expression values name]
    have referenceMeaning : meaning holds (bind ambient name candidate) (Value.reference name : Value Symbol Guard) = candidate := by
      rw [meaning]; simp only [InternedGuardedBudget.bind, ↓reduceIte]
    simp only [List.map_cons, referenceMeaning]
    exact InternedGuardedSmartBudgetValues.body_bind_fresh holds expression values state context.normal.facts.coherent
      context.inputs ambient name candidate fresh
  constructor
  · rw [filter_least holds ambient name value state context.normal.facts available]
    apply congrArg BinderBudgetLanguage.mu
    funext candidate
    exact interpreted candidate
  · rw [filter_empty holds ambient name value state context.normal.facts available]
    exact interpreted (fun _ _ => False)

/-- A decoded deep capture is also one of the already proved surviving free captures. -/
theorem deep_capture_free (expression : Syntax Symbol Guard) (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (available : Values state values) (name : Reference)
    (member : name ∈ InternedRecordDepthCallback.captured expression values) :
    name ∈ InternedProfileCallbackForm.captures
      (InternedFreeNameForm.symbolic expression (values.map InternedRootProfile.profile) (values.map Value.free)) := by
  apply (InternedRecordDepthCallback.captures_free expression values state coherent available name).mp
  rw [← InternedFreshOrdinaryDepthComposition.lower_captures, InternedFreeNameSemantics.lower_member]
  apply List.mem_append_right
  change Sum.inr name ∈ (InternedRecordDepthCallback.symbolic expression values).deep
  change name ∈ InternedProfileCallbackForm.captures (InternedRecordDepthCallback.symbolic expression values).deep at member
  rw [← InternedFreshOrdinaryDepthComposition.lower_captures, InternedFreeNameSemantics.lower_member] at member
  exact member

/-- The actual ordinary probe selects the same deep-local branch as the complete symbolic source shape. -/
theorem uses_source (expression : Syntax Symbol Guard) (values : List (Value Symbol Guard))
    (depth ordinary : Value Symbol Guard) (state : State Symbol Guard) (context : Context state values)
    (fresh : .uninterned (ordinaryLevel depth) ∉ InternedProfileCallbackForm.captures
      (InternedFreeNameForm.symbolic expression (values.map InternedRootProfile.profile) (values.map Value.free)))
    (observed : InternedFreshOrdinaryDepthHeap.Observed (InternedRecordDepthCallback.captured expression values)
      (InternedRecordDepthCallback.uses expression values) (.uninterned (ordinaryLevel depth)) ordinary) :
    InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary =
      InternedDepthSemantics.hasLocal (InternedRecordDepthCallback.symbolic expression values).deep := by
  have freshDeep : .uninterned (ordinaryLevel depth) ∉ InternedRecordDepthCallback.captured expression values :=
    fun member => fresh (deep_capture_free expression values state context.normal.facts.coherent context.inputs _ member)
  have own := InternedFreshOrdinaryDepthHeap.observed_own _ _ _ _ observed freshDeep
  apply Bool.eq_iff_iff.mpr
  simpa only [InternedFreshOrdinaryDepthHeap.usesLocal, decide_eq_true_eq,
    InternedFreshOrdinaryDepthComposition.hasLocal_uses, InternedRecordDepthCallback.uses] using own

end MicroCFTA.InternedGuardedBudgetCallback
