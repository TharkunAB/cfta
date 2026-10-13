import MicroCFTA.InternedNestedMissReadback

/-!
# Exact empty results of source recursive cleanup

Raw recursive construction retains its record. Smart cleanup returns
EmptyNode exactly for an empty body or a bare reference to the newly
reserved identity. Actual miss readback gives this classification for
arbitrary successful source callback executions.
-/
namespace MicroCFTA.InternedCleanupEmptiness
open Cache InternedConstructorTemplates InternedNestedConstruction InternedRecordCoherence
open InternedNestedMissReadback
open InternedBinderProtocol (NodeKey)

/-- The source smart constructor has exactly two empty-result body cases. -/
theorem finish_empty_iff (smart : Bool) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard) :
    finish smart (.mu entry body depth ordinary) = .empty ↔
      smart = true ∧ (body = .empty ∨ body = .reference (.interned entry.identity)) := by
  cases smart with
  | false => simp [finish]
  | true =>
      by_cases unused : .interned entry.identity ∉ body.free
      · simp only [finish, cleanup, unused, ↓reduceIte, true_and]
        have notSelf : body ≠ .reference (.interned entry.identity) := by
          intro same
          subst body
          simp [Value.free] at unused
        simp [notSelf]
      · have notEmpty : body ≠ .empty := by
          intro same
          subst body
          simp [Value.free] at unused
        by_cases self : body.referenceOf = .ref (.interned entry.identity)
        · have bodySame := InternedCleanupAge.reference_eq body _ self
          simp [finish, cleanup, bodySame, Value.free, Value.referenceOf]
        · have notSelf : body ≠ .reference (.interned entry.identity) := by
            intro same
            subst body
            exact self rfl
          simp [finish, cleanup, unused, self, notEmpty, notSelf]

/-- A bare reference survives recursive cleanup exactly when it names another binder. -/
theorem finish_reference_iff (smart : Bool) (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard) (name : InternedBinderProtocol.Reference) :
    finish smart (.mu entry body depth ordinary) = .reference name ↔
      smart = true ∧ body = .reference name ∧ name ≠ .interned entry.identity := by
  cases smart with
  | false => simp [finish]
  | true =>
      simp only [true_and]
      by_cases unused : .interned entry.identity ∉ body.free
      · have finished : finish true (.mu entry body depth ordinary) = body := by
          simp [finish, cleanup, unused]
        rw [finished]
        constructor
        · intro same
          refine ⟨same, ?_⟩
          intro equal
          apply unused
          rw [same, equal]
          simp [Value.free]
        · exact And.left
      · have cannot : ¬ (body = .reference name ∧ name ≠ .interned entry.identity) := by
          rintro ⟨same, different⟩
          apply unused
          rw [same]
          simp [Value.free, Ne.symm different]
        rw [iff_false_right cannot]
        simp only [finish, cleanup, unused, ↓reduceIte]
        split <;> simp

/-- Empty reference identity is equivalent to the same two exact smart body cases. -/
theorem finish_empty_reference_iff (smart : Bool) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard) :
    (finish smart (.mu entry body depth ordinary)).referenceOf = .empty ↔
      smart = true ∧ (body = .empty ∨ body = .reference (.interned entry.identity)) := by
  have empty : ∀ value : Value Symbol Guard, value.referenceOf = .empty ↔ value = .empty := by
    intro value
    cases value <;> simp [Value.referenceOf]
  rw [empty, finish_empty_iff]

/-- An actual source miss returns EmptyNode only after one of the exact two body results. -/
theorem request_miss_empty [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (body : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (depth ordinary : Value Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state)
    (missing : state.nodes.table (muKey depth ordinary) = none)
    (final : State Symbol Guard)
    (completed : request smart depth ordinary (callback body environment) state = .done .empty final) :
    let entry := (Cache.intern state.nodes (muKey depth ordinary)).1
    ∃ actual afterBody,
      callback body environment (.interned entry.identity)
        {state with nodes := (Cache.intern state.nodes (muKey depth ordinary)).2} = .done actual afterBody ∧
      smart = true ∧ (actual = .empty ∨ actual = .reference (.interned entry.identity)) := by
  obtain ⟨actual, afterBody, bodyDone, _, same, _⟩ :=
    request_miss smart body environment depth ordinary state coherent missing .empty final completed
  exact ⟨actual, afterBody, bodyDone,
    (finish_empty_iff smart (Cache.intern state.nodes (muKey depth ordinary)).1 actual depth ordinary).mp same.symm⟩

end MicroCFTA.InternedCleanupEmptiness
