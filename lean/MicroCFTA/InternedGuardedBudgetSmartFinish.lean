import MicroCFTA.InternedGuardedBudgetSelfFilter
import MicroCFTA.InternedDeepFreeDepth

/-!
# Exact budgets of actual filtered binder cleanup

Root self alternatives have empty language when their local language is
empty. A smart binder retains its step precisely when the local occurs
deeply. The existing source normalization facts decide both branches.
-/
namespace MicroCFTA.InternedGuardedBudget
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedFacts InternedNestedProvenance InternedStoredMuOrigins
open InternedBinderProtocol (Reference NodeKey)
open Language

/-- Actual root filtering retains the body language when its local language is empty. -/
theorem filter_empty [DecidableEq (EdgeKey Symbol Guard)] (holds : Guard → Term Symbol → Bool)
    (environment : Env Symbol) (name : Reference) (body : Value Symbol Guard) (state : State Symbol Guard)
    (facts : Facts state) (available : Available state body) :
    meaning holds (bind environment name (fun _ _ => False)) (run (withoutSelfReference name body) state).1 =
      meaning holds (bind environment name (fun _ _ => False)) body := by
  cases body with
  | empty | reference | node | mu => rfl
  | union entry members depth free =>
      by_cases selected : members.any (fun member => member.referenceOf == .ref name) = true
      · simp only [withoutSelfReference, selected, ↓reduceIte]
        have inputs : Values state (members.filter (fun member => member.referenceOf != .ref name)) := by
          intro member present
          exact available.children member (List.mem_filter.mp present).1
        funext budget term
        apply propext
        rw [makeUnion_exact state facts holds _ _ inputs budget term,
          (laws holds (bind environment name (fun _ _ => False)) budget).union]
        constructor
        · rintro ⟨member, present, accepted⟩
          exact ⟨member, (List.mem_filter.mp present).1, accepted⟩
        · rintro ⟨member, present, accepted⟩
          refine ⟨member, List.mem_filter.mpr ⟨present, ?_⟩, accepted⟩
          have different : member.referenceOf ≠ .ref name := by
            intro same
            have literal := (referenceOf_self_iff name member).mp same
            subst member
            simp only [meaning, bind, ↓reduceIte] at accepted
          simpa using different
      · simp only [withoutSelfReference, selected]
        rfl

/-- A deep local occurrence prevents actual smart cleanup from deleting the Mu step. -/
theorem finish_filter_used [DecidableEq (EdgeKey Symbol Guard)] (holds : Guard → Term Symbol → Bool)
    (environment : Env Symbol) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (state : State Symbol Guard) (normal : Normal state) (available : Available state body)
    (used : .interned entry.identity ∈ InternedDeepFreeDepth.deepNames body) :
    meaning holds environment (InternedNestedConstruction.finish true
      (.mu entry (run (withoutSelfReference (.interned entry.identity) body) state).1 depth ordinary)) =
      meaning holds environment (.mu entry body depth ordinary) := by
  have nonbare : body ≠ .reference (.interned entry.identity) := by
    intro same
    simp only [same, InternedDeepFreeDepth.deepNames, List.not_mem_nil] at used
  have filteredUsed := (InternedDeepFreeDepth.filter_free (.interned entry.identity) body state normal available nonbare).mpr used
  have filteredNonbare : (run (withoutSelfReference (.interned entry.identity) body) state).1.referenceOf ≠
      .ref (.interned entry.identity) := by
    intro same
    apply nonbare
    exact (InternedFilterSelfReference.filter_self_iff (.interned entry.identity) body state
      normal.facts.coherent normal.flat available).mp ((referenceOf_self_iff _ _).mp same)
  simp only [InternedNestedConstruction.finish, cleanup, filteredUsed, not_true_eq_false, ↓reduceIte, filteredNonbare]
  exact filter_mu holds environment entry body depth ordinary state normal.facts available

/-- Without a deep local, actual smart cleanup returns exactly the body with an empty local language. -/
theorem finish_filter_unused [DecidableEq (EdgeKey Symbol Guard)] (holds : Guard → Term Symbol → Bool)
    (environment : Env Symbol) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (state : State Symbol Guard) (normal : Normal state) (available : Available state body)
    (unused : .interned entry.identity ∉ InternedDeepFreeDepth.deepNames body) :
    meaning holds environment (InternedNestedConstruction.finish true
      (.mu entry (run (withoutSelfReference (.interned entry.identity) body) state).1 depth ordinary)) =
      meaning holds (bind environment (.interned entry.identity) (fun _ _ => False)) body := by
  by_cases bare : body = .reference (.interned entry.identity)
  · subst body
    simp only [withoutSelfReference, run, InternedNestedConstruction.finish, cleanup, Value.free,
      List.mem_singleton, not_true_eq_false, ↓reduceIte, Value.referenceOf, meaning, bind]
  · have filteredUnused : .interned entry.identity ∉
        (run (withoutSelfReference (.interned entry.identity) body) state).1.free :=
      fun member => unused ((InternedDeepFreeDepth.filter_free (.interned entry.identity) body state normal available bare).mp member)
    rw [InternedNestedConstruction.finish, cleanup, ite_eq_left filteredUnused]
    have built := InternedTemplateProvenance.withoutSelfReference_available (.interned entry.identity) body state
      normal.facts.coherent normal.facts.cached available
    apply Eq.trans (b := meaning holds (bind environment (.interned entry.identity) (fun _ _ => False))
      (run (withoutSelfReference (.interned entry.identity) body) state).1)
    · apply meaning_free holds _ _ built.1 built.2.2
      intro name member
      have different : name ≠ .interned entry.identity := fun same => filteredUnused (same ▸ member)
      simp only [bind, different, ↓reduceIte]
    · exact filter_empty holds environment (.interned entry.identity) body state normal.facts available

/-- Actual filtered binder finish has the exact raw or empty-local budget branch. -/
theorem finish_filter_exact [DecidableEq (EdgeKey Symbol Guard)] (holds : Guard → Term Symbol → Bool)
    (environment : Env Symbol) (smart : Bool) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (state : State Symbol Guard) (normal : Normal state) (available : Available state body) :
    meaning holds environment (InternedNestedConstruction.finish smart
      (.mu entry (run (withoutSelfReference (.interned entry.identity) body) state).1 depth ordinary)) =
      if smart ∧ .interned entry.identity ∉ InternedDeepFreeDepth.deepNames body then
        meaning holds (bind environment (.interned entry.identity) (fun _ _ => False)) body
      else meaning holds environment (.mu entry body depth ordinary) := by
  cases smart with
  | false =>
      simp only [Bool.false_eq_true, false_and, ↓reduceIte, InternedNestedConstruction.finish]
      exact filter_mu holds environment entry body depth ordinary state normal.facts available
  | true =>
      by_cases used : .interned entry.identity ∈ InternedDeepFreeDepth.deepNames body
      · simpa only [Bool.true_eq, true_and, used, not_true_eq_false, ↓reduceIte] using
          finish_filter_used holds environment entry body depth ordinary state normal available used
      · simpa only [Bool.true_eq, true_and, used, not_false_eq_true, ↓reduceIte] using
          finish_filter_unused holds environment entry body depth ordinary state normal available used

end MicroCFTA.InternedGuardedBudget
