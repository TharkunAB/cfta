import MicroCFTA.InternedBoundaryAge
import MicroCFTA.InternedNestedMissReadback

/-!
# Fresh recursive records hidden from the ordinary boundary profile

Absence of the newly reserved Mu boundary forces one of the two smart
cleanup branches. Returning an unused body preserves every forbidden-atom
condition of the output. No age condition on ordinary node identities is
needed by this classification.
-/
namespace MicroCFTA.InternedBoundaryCleanup
open Cache InternedConstructorTemplates InternedNestedConstruction InternedRecordCoherence
open InternedBoundaryAtoms InternedNestedMissReadback
open InternedBinderProtocol (NodeKey NodeRef)

/-- If the fresh Mu boundary is absent, cleanup must return an unused body or remove a bare self reference. -/
theorem finish_cases (smart : Bool) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (absent : .mu entry.identity ∉ atoms (finish smart (.mu entry body depth ordinary))) :
    smart = true ∧
      ((finish smart (.mu entry body depth ordinary) = body ∧ .interned entry.identity ∉ body.free) ∨
        (finish smart (.mu entry body depth ordinary) = .empty ∧ body = .reference (.interned entry.identity))) := by
  cases smart with
  | false => simp [finish, atoms] at absent
  | true =>
      refine ⟨rfl, ?_⟩
      by_cases unused : .interned entry.identity ∉ body.free
      · exact Or.inl ⟨by simp [finish, cleanup, unused], unused⟩
      · by_cases self : body.referenceOf = .ref (.interned entry.identity)
        · exact Or.inr ⟨by simp [finish, cleanup, unused, self], InternedCleanupAge.reference_eq body _ self⟩
        · have retained : finish true (.mu entry body depth ordinary) = .mu entry body depth ordinary := by
            simp only [finish, cleanup, unused, self, ↓reduceIte]
          simp only [retained, atoms, List.mem_singleton] at absent
          exact False.elim (absent trivial)

/-- A successful source miss with no fresh Mu output preserves its forbidden-atom condition in the unused-body branch. -/
theorem request_miss_cases [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (body : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (depth ordinary : Value Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state)
    (missing : state.nodes.table (muKey depth ordinary) = none)
    (value : Value Symbol Guard) (final : State Symbol Guard)
    (completed : request smart depth ordinary (callback body environment) state = .done value final)
    (forbidden : NodeRef → Prop)
    (freshForbidden : forbidden (.mu (Cache.intern state.nodes (muKey depth ordinary)).1.identity))
    (absent : ∀ atom, forbidden atom → atom ∉ atoms value) :
    let entry := (Cache.intern state.nodes (muKey depth ordinary)).1
    ∃ actual afterBody,
      callback body environment (.interned entry.identity)
        {state with nodes := (Cache.intern state.nodes (muKey depth ordinary)).2} = .done actual afterBody ∧
      smart = true ∧
      ((value = actual ∧ .interned entry.identity ∉ actual.free ∧
          ∀ atom, forbidden atom → atom ∉ atoms actual) ∨
        (value = .empty ∧ actual = .reference (.interned entry.identity))) := by
  obtain ⟨actual, afterBody, bodyDone, _, same, _⟩ :=
    request_miss smart body environment depth ordinary state coherent missing value final completed
  have localAbsent : .mu (Cache.intern state.nodes (muKey depth ordinary)).1.identity ∉
      atoms (finish smart (.mu (Cache.intern state.nodes (muKey depth ordinary)).1 actual depth ordinary)) := by
    rw [← same]
    exact absent _ freshForbidden
  obtain ⟨smartTrue, cases⟩ := finish_cases smart (Cache.intern state.nodes (muKey depth ordinary)).1 actual depth ordinary localAbsent
  refine ⟨actual, afterBody, bodyDone, smartTrue, ?_⟩
  rcases cases with ⟨bodyReturn, unused⟩ | ⟨emptyReturn, bare⟩
  · have equal := same.trans bodyReturn
    exact Or.inl ⟨equal, unused, fun atom selected => equal ▸ absent atom selected⟩
  · exact Or.inr ⟨same.trans emptyReturn, bare⟩

end MicroCFTA.InternedBoundaryCleanup
