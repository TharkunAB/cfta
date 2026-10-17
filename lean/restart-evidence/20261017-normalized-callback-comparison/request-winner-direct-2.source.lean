import MicroCFTA.InternedNestedRequestFacts

/-!
# Exact selected record after a successful Mu request

The hit branch reads its existing record. The miss branch reads the actual
keep-first winner after the callback. No callback result law is required.
-/
namespace MicroCFTA.SourceCurrentNativeRequestWinner
open Cache InternedConstructorTemplates
open InternedNestedConstruction (Outcome request finish)
open InternedBinderProtocol (Reference)

/-- Every successful request returns cleanup of its exact final stored winner. -/
theorem winner [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool)
    (depth ordinary : Value Symbol Guard)
    (callback : Reference → State Symbol Guard → Outcome Symbol Guard (Value Symbol Guard))
    (before : State Symbol Guard) (value : Value Symbol Guard) (after : State Symbol Guard)
    (actual : request smart depth ordinary callback before = .done value after) :
    ∃ selected, after.nodeRecords (muKey depth ordinary) = some selected ∧
      value = finish smart selected := by
  cases installed : before.nodes.table (muKey depth ordinary) with
  | some entry =>
      cases found : before.nodeRecords (muKey depth ordinary) with
      | none => simp only [request, installed, found] at actual; cases actual
      | some selected =>
          simp only [request, installed, found, Outcome.done.injEq] at actual
          obtain ⟨rfl, rfl⟩ := actual
          exact ⟨selected, found, rfl⟩
  | none =>
      let entry := Cache.intern before.nodes (muKey depth ordinary)
      let allocated := {before with nodes := entry.2}
      simp only [request, installed] at actual
      change (callback (.interned entry.1.identity) allocated).bind _ = .done value after at actual
      cases bodyDone : callback (.interned entry.1.identity) allocated with
      | pending key current => simp only [bodyDone, Outcome.bind] at actual; cases actual
      | done body afterBody =>
          obtain ⟨selected, present⟩ := keepFirst_present afterBody.nodeRecords (muKey depth ordinary)
            (.mu entry.1 body depth ordinary)
          simp only [bodyDone, Outcome.bind, Outcome.done.injEq] at actual
          obtain ⟨rfl, rfl⟩ := actual
          refine ⟨selected, present, ?_⟩
          change finish smart ((keepFirst afterBody.nodeRecords (muKey depth ordinary)
            (.mu entry.1 body depth ordinary) (muKey depth ordinary)).getD (.mu entry.1 body depth ordinary)) = _
          rw [present]

end MicroCFTA.SourceCurrentNativeRequestWinner
