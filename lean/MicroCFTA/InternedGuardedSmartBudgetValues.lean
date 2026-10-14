import MicroCFTA.InternedGuardedSmartBudgetSyntaxSupport
import MicroCFTA.InternedGuardedSmartBudgetRename
import MicroCFTA.InternedGuardedBudgetSupport
import MicroCFTA.InternedRecordDepthCallback

/-!
# Actual captured records satisfy smart-budget support

Complete records supply the existing root and deep shapes. Coherent cached
free names bound every ambient budget read. Only surviving symbolic captures
need freshness when a callback supplies its local reference.
-/
namespace MicroCFTA.InternedGuardedSmartBudgetValues
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax)
open InternedNestedProvenance (Values)
open InternedBinderProtocol (Reference)
open InternedGuardedBudget (Env meaning)
open InternedGuardedSmartBudgetSupport
open BinderBudgetLanguage (Lang)
open InternedRecordDepthShape (shape)

/-- Every actual record has its decoded shape's full budget root bound. -/
theorem shape_upper (holds : Guard → Term Symbol → Bool) (environment : Env Symbol) (value : Value Symbol Guard) :
    Upper environment (shape value) (meaning holds environment value) := by
  cases value with
  | empty =>
      rw [shape, meaning]
      exact fun _ _ _ impossible => impossible.elim
  | reference name =>
      rw [shape, meaning]
      exact fun _ budget term accepted => ⟨name, by simp, accepted⟩
  | node | mu => intro impossible; simp only [shape, Bool.true_eq_false] at impossible
  | union entry members depth free =>
      rw [shape, meaning]
      have bound := alternatives_upper environment members shape (meaning holds environment) (fun member present => by
        have smaller := List.sizeOf_lt_of_mem present
        exact shape_upper holds environment member)
      simpa only [Upper, InternedRecordDepthShape.shapes_map] using bound
termination_by sizeOf value
decreasing_by all_goals simp_wf; all_goals omega

/-- A coherent available capture has exact shape root bounds and ambient budget support. -/
theorem value_related (holds : Guard → Term Symbol → Bool) (value : Value Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state) (available : Available state value) (before after : Env Symbol) :
    Related (shape value) before after (meaning holds before value) (meaning holds after value) := by
  refine ⟨shape_upper holds before value, shape_upper holds after value, ?_⟩
  intro agree
  apply InternedGuardedBudget.meaning_free holds value state coherent available before after
  intro name named
  exact agree name ((InternedRecordDepthShape.shape_free value state coherent available name).mpr named)

/-- Ordered actual captures satisfy the full lexical smart-budget input relation. -/
theorem values_inputs (holds : Guard → Term Symbol → Bool) (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (available : Values state values) (before after : Env Symbol) :
    Inputs (values.map shape) before after (values.map (meaning holds before)) (values.map (meaning holds after)) := by
  intro index
  cases found : values[index]? with
  | none =>
      simpa only [List.getElem?_map, found, Option.map_none, Option.getD_none] using related_empty before after
  | some value =>
      simpa only [List.getElem?_map, found, Option.map_some, Option.getD_some] using
        value_related holds value state coherent (available value (List.mem_of_getElem? found)) before after

/-- A symbolic body reads external budget languages only at its surviving captured free names. -/
theorem body_captures (holds : Guard → Term Symbol → Bool) (body : Syntax Symbol Guard)
    (values : List (Value Symbol Guard)) (state : State Symbol Guard) (coherent : Coherent state)
    (available : Values state values) (before after : Env Symbol) (candidate : Lang Symbol)
    (agree : Agree before after (InternedProfileCallbackForm.captures
      (InternedFreeNameForm.symbolic body (values.map InternedRootProfile.profile) (values.map Value.free)))) :
    InternedGuardedSmartBudget.evaluate holds
      (⟨[Sum.inl ()], [], false, 0⟩ :: (values.map shape).map (InternedDepthSemantics.Shape.map Sum.inr))
      (candidate :: values.map (meaning holds before)) body =
    InternedGuardedSmartBudget.evaluate holds
      (⟨[Sum.inl ()], [], false, 0⟩ :: (values.map shape).map (InternedDepthSemantics.Shape.map Sum.inr))
      (candidate :: values.map (meaning holds after)) body := by
  have inputs := inputs_binder _ before after _ _ (values_inputs holds values state coherent available before after) candidate candidate
  apply (evaluate_related holds body _ _ _ _ _ inputs).support
  intro name member
  cases name with
  | inl token => rfl
  | inr name =>
      apply agree name
      apply (InternedRecordDepthCallback.captures_free body values state coherent available name).mp
      rw [← InternedFreshOrdinaryDepthComposition.lower_captures]
      exact (InternedFreeNameSemantics.lower_member _ name).mpr member

/-- Binding a name absent from surviving captures retains the complete symbolic body budget language. -/
theorem body_bind_fresh (holds : Guard → Term Symbol → Bool) (body : Syntax Symbol Guard)
    (values : List (Value Symbol Guard)) (state : State Symbol Guard) (coherent : Coherent state)
    (available : Values state values) (environment : Env Symbol) (name : Reference) (candidate : Lang Symbol)
    (fresh : name ∉ InternedProfileCallbackForm.captures
      (InternedFreeNameForm.symbolic body (values.map InternedRootProfile.profile) (values.map Value.free))) :
    InternedGuardedSmartBudget.evaluate holds
      (⟨[Sum.inl ()], [], false, 0⟩ :: (values.map shape).map (InternedDepthSemantics.Shape.map Sum.inr))
      (candidate :: values.map (meaning holds (InternedGuardedBudget.bind environment name candidate))) body =
    InternedGuardedSmartBudget.evaluate holds
      (⟨[Sum.inl ()], [], false, 0⟩ :: (values.map shape).map (InternedDepthSemantics.Shape.map Sum.inr))
      (candidate :: values.map (meaning holds environment)) body := by
  apply body_captures holds body values state coherent available _ _ candidate
  intro other member
  have different : other ≠ name := fun same => fresh (same ▸ member)
  simp only [InternedGuardedBudget.bind, different, ↓reduceIte]

/-- Actual supplied reference shapes and the symbolic local give the same smart-budget interpretation. -/
theorem body_supplied (holds : Guard → Term Symbol → Bool) (body : Syntax Symbol Guard)
    (values : List (Value Symbol Guard)) (argument : Reference) (languages : List (Lang Symbol)) :
    InternedGuardedSmartBudget.evaluate holds ((Value.reference argument :: values).map shape) languages body =
      InternedGuardedSmartBudget.evaluate holds
        (⟨[Sum.inl ()], [], false, 0⟩ :: (values.map shape).map (InternedDepthSemantics.Shape.map Sum.inr)) languages body := by
  have mapped := InternedGuardedSmartBudget.evaluate_map (InternedProfileCallbackForm.supply argument) holds body
    (⟨[Sum.inl ()], [], false, 0⟩ :: (values.map shape).map (InternedDepthSemantics.Shape.map Sum.inr)) languages
  simpa [shape, InternedDepthSemantics.Shape.map, InternedProfileCallbackForm.supply,
    List.map_map, Function.comp_def] using mapped

end MicroCFTA.InternedGuardedSmartBudgetValues
