import MicroCFTA.InternedGuardedSyntaxSupport
import MicroCFTA.InternedGuardedLanguageSupport
import MicroCFTA.InternedFreeNameForm
import MicroCFTA.InternedNestedProvenance

/-!
# Stored inputs satisfy the source profile and support bounds

Literal root profiles bound the independent language of every stored value.
Coherent available values also satisfy the free-name support bound. The
complete source support law therefore applies to actual lexical captures.
-/
namespace MicroCFTA.InternedGuardedProfileSupport
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax)
open InternedNestedProvenance (Values)
open InternedGuardedLanguage (Env meaning)
open InternedGuardedAbstractSupport InternedGuardedSyntaxSupport
open BinderLanguage (Lang)
open InternedBinderProtocol (Reference)

/-- Actual union profiles use the same ordered combination as the pure source analysis. -/
theorem many_profiles (values : List (Value Symbol Guard)) :
    InternedRootProfile.many values = InternedProfileSemantics.combineMany (values.map InternedRootProfile.profile) := by
  induction values with
  | nil => rw [InternedRootProfile.many, List.map_nil, InternedProfileSemantics.combineMany]
  | cons first rest ih =>
      rw [InternedRootProfile.many, List.map_cons, InternedProfileSemantics.combineMany, ih]
      cases InternedRootProfile.profile first <;> cases InternedProfileSemantics.combineMany (rest.map InternedRootProfile.profile) <;> rfl

/-- A pure actual root profile bounds the full independent guarded language. -/
theorem profile_upper (holds : Guard → Term Symbol → Bool) (environment : Env Symbol) (value : Value Symbol Guard) :
    Upper environment (InternedRootProfile.profile value) (meaning holds environment value) := by
  cases value with
  | empty =>
      rw [InternedRootProfile.profile, meaning]
      exact fun _ impossible => False.elim impossible
  | reference name =>
      rw [InternedRootProfile.profile, meaning]
      exact fun term accepted => ⟨name, by simp, accepted⟩
  | node => rw [InternedRootProfile.profile]; trivial
  | mu => rw [InternedRootProfile.profile]; trivial
  | union entry members depth free =>
      rw [InternedRootProfile.profile, many_profiles, meaning]
      apply alternatives_upper environment members InternedRootProfile.profile (meaning holds environment)
      intro member present
      have smaller := List.sizeOf_lt_of_mem present
      exact profile_upper holds environment member
termination_by sizeOf value
decreasing_by all_goals simp_wf; all_goals omega

/-- Actual coherent available inputs satisfy both semantic analysis bounds. -/
theorem value_related (holds : Guard → Term Symbol → Bool) (value : Value Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state) (available : Available state value) (before after : Env Symbol) :
    Related (InternedRootProfile.profile value) value.free before after (meaning holds before value) (meaning holds after value) :=
  ⟨profile_upper holds before value, profile_upper holds after value,
    InternedGuardedLanguage.meaning_free holds value state coherent available before after⟩

/-- Lists of actual coherent available captures satisfy the full lexical input relation. -/
theorem values_inputs (holds : Guard → Term Symbol → Bool) (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (available : Values state values) (before after : Env Symbol) :
    Inputs (values.map InternedRootProfile.profile) (values.map Value.free) before after
      (values.map (meaning holds before)) (values.map (meaning holds after)) := by
  intro index
  cases found : values[index]? with
  | none =>
      simpa only [List.getElem?_map, found, Option.map_none, Option.getD_none] using related_empty before after
  | some value =>
      simpa only [List.getElem?_map, found, Option.map_some, Option.getD_some] using
        value_related holds value state coherent (available value (List.mem_of_getElem? found)) before after

/-- Only the source analysis's surviving names can affect a plan over actual captures. -/
theorem evaluate_free (holds : Guard → Term Symbol → Bool) (expression : Syntax Symbol Guard)
    (values : List (Value Symbol Guard)) (state : State Symbol Guard) (coherent : Coherent state)
    (available : Values state values) (before after : Env Symbol)
    (agree : Agree before after (InternedFreeNameSemantics.evaluate expression
      (values.map InternedRootProfile.profile) (values.map Value.free))) :
    InternedGuardedSyntax.evaluate holds (values.map (meaning holds before)) expression =
      InternedGuardedSyntax.evaluate holds (values.map (meaning holds after)) expression :=
  (evaluate_related holds expression _ _ before after _ _ (values_inputs holds values state coherent available before after)).support agree

/-- A binder body reads external names only from its surviving symbolic capture set. -/
theorem body_captures (holds : Guard → Term Symbol → Bool) (body : Syntax Symbol Guard)
    (values : List (Value Symbol Guard)) (state : State Symbol Guard) (coherent : Coherent state)
    (available : Values state values) (before after : Env Symbol) (candidate : Lang Symbol)
    (agree : Agree before after (InternedProfileCallbackForm.captures
      (InternedFreeNameForm.symbolic body (values.map InternedRootProfile.profile) (values.map Value.free)))) :
    InternedGuardedSyntax.evaluate holds (candidate :: values.map (meaning holds before)) body =
      InternedGuardedSyntax.evaluate holds (candidate :: values.map (meaning holds after)) body := by
  have inputs := inputs_binder _ _ before after _ _ (values_inputs holds values state coherent available before after) candidate candidate
  apply (evaluate_related holds body _ _ _ _ _ _ inputs).support
  intro name member
  cases name with
  | inl token => rfl
  | inr name =>
      apply agree name
      have lowered (symbols : List (Sum Unit Reference)) :
          InternedProfileCallbackForm.captures symbols = InternedFreeNameSemantics.lower symbols := by
        unfold InternedProfileCallbackForm.captures InternedFreeNameSemantics.lower
        congr 1
        funext symbol
        cases symbol <;> rfl
      rw [lowered]
      exact (InternedFreeNameSemantics.lower_member _ name).mpr member

/-- A name absent from surviving captures can be bound without changing any body result. -/
theorem body_bind_fresh (holds : Guard → Term Symbol → Bool) (body : Syntax Symbol Guard)
    (values : List (Value Symbol Guard)) (state : State Symbol Guard) (coherent : Coherent state)
    (available : Values state values) (environment : Env Symbol) (name : Reference) (candidate : Lang Symbol)
    (fresh : name ∉ InternedProfileCallbackForm.captures
      (InternedFreeNameForm.symbolic body (values.map InternedRootProfile.profile) (values.map Value.free))) :
    InternedGuardedSyntax.evaluate holds (candidate :: values.map (meaning holds (InternedGuardedLanguage.bind environment name candidate))) body =
      InternedGuardedSyntax.evaluate holds (candidate :: values.map (meaning holds environment)) body := by
  apply body_captures holds body values state coherent available _ _ candidate
  intro other member
  have different : other ≠ name := fun same => fresh (same ▸ member)
  simp only [InternedGuardedLanguage.bind, different, ↓reduceIte]

end MicroCFTA.InternedGuardedProfileSupport
