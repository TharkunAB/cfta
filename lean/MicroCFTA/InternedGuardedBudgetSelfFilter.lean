import MicroCFTA.InternedGuardedBudgetConstructors

/-!
# Actual root-self filtering retains budgeted Mu languages

Deleted root alternatives read the candidate recursive language. An upward
candidate already contains each smaller-budget self term. Actual union
reconstruction retains all other guarded alternatives at the same budget.
-/
namespace MicroCFTA.InternedGuardedBudget
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedFacts InternedNestedProvenance Language
open InternedBinderProtocol (Reference NodeKey)

/-- Actual root-self filtering retains the upward candidates closed under one binder step. -/
theorem filter_closed [DecidableEq (EdgeKey Symbol Guard)] (holds : Guard → Term Symbol → Bool)
    (environment : Env Symbol) (name : Reference) (body : Value Symbol Guard) (state : State Symbol Guard)
    (facts : Facts state) (available : Available state body) (candidate : BinderBudgetLanguage.Lang Symbol)
    (upward : BinderBudgetLanguage.Upward candidate) :
    BinderBudgetLanguage.Included
        (BinderBudgetLanguage.shift (meaning holds (bind environment name candidate) (run (withoutSelfReference name body) state).1)) candidate ↔
      BinderBudgetLanguage.Included (BinderBudgetLanguage.shift (meaning holds (bind environment name candidate) body)) candidate := by
  cases body with
  | empty | reference | node | mu => rfl
  | union entry members depth free =>
      by_cases selected : members.any (fun member => member.referenceOf == .ref name) = true
      · simp only [withoutSelfReference, selected, ↓reduceIte]
        have inputs : Values state (members.filter (fun member => member.referenceOf != .ref name)) := by
          intro member present
          exact available.children member (List.mem_filter.mp present).1
        have normalized := makeUnion_exact state facts holds (bind environment name candidate) _ inputs
        constructor
        · rintro closed budget term ⟨smaller, less, accepted⟩
          obtain ⟨member, present, accepted⟩ :=
            ((laws holds (bind environment name candidate) smaller).union entry members depth free term).mp accepted
          by_cases same : member.referenceOf = .ref name
          · have literal := (referenceOf_self_iff name member).mp same
            subst member
            apply upward smaller budget (Nat.le_of_lt less) term
            simpa only [meaning, bind, ↓reduceIte] using accepted
          · apply closed budget term
            refine ⟨smaller, less, (normalized smaller term).mpr ?_⟩
            exact ⟨member, List.mem_filter.mpr ⟨present, by simpa using same⟩, accepted⟩
        · rintro closed budget term ⟨smaller, less, accepted⟩
          obtain ⟨member, present, accepted⟩ := (normalized smaller term).mp accepted
          exact closed budget term ⟨smaller, less,
            ((laws holds (bind environment name candidate) smaller).union entry members depth free term).mpr
              ⟨member, (List.mem_filter.mp present).1, accepted⟩⟩
      · simp only [withoutSelfReference, selected]
        exact Iff.rfl

/-- Actual callback filtering preserves the complete budgeted least binder language. -/
theorem filter_least [DecidableEq (EdgeKey Symbol Guard)] (holds : Guard → Term Symbol → Bool)
    (environment : Env Symbol) (name : Reference) (body : Value Symbol Guard) (state : State Symbol Guard)
    (facts : Facts state) (available : Available state body) :
    BinderBudgetLanguage.mu (fun candidate => meaning holds (bind environment name candidate) (run (withoutSelfReference name body) state).1) =
      BinderBudgetLanguage.mu (fun candidate => meaning holds (bind environment name candidate) body) := by
  funext budget term
  apply propext
  constructor
  · intro accepted candidate upward closed
    exact accepted candidate upward ((filter_closed holds environment name body state facts available candidate upward).mpr closed)
  · intro accepted candidate upward closed
    exact accepted candidate upward ((filter_closed holds environment name body state facts available candidate upward).mp closed)

/-- The actual filtered and original stored Mu bodies have equal languages at every budget. -/
theorem filter_mu [DecidableEq (EdgeKey Symbol Guard)] (holds : Guard → Term Symbol → Bool) (environment : Env Symbol)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard) (state : State Symbol Guard)
    (facts : Facts state) (available : Available state body) :
    meaning holds environment (.mu entry (run (withoutSelfReference (.interned entry.identity) body) state).1 depth ordinary) =
      meaning holds environment (.mu entry body depth ordinary) := by
  rw [meaning, meaning]
  exact filter_least holds environment (.interned entry.identity) body state facts available

end MicroCFTA.InternedGuardedBudget
