import MicroCFTA.InternedGuardedBudgetExecution
import MicroCFTA.InternedGuardedStoredExecution

/-!
# Exact smart budgets of actual stored execution

Actual stored plans run with their complete captured record shapes and
budget languages. Source execution derives both probe heaps and the exact
smart-plan language. Raw-plan inclusion remains a separate obligation.
-/
namespace MicroCFTA.InternedGuardedBudgetStoredExecution
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedStoredSubstitution (Environment Replacements leaves input encode)
open InternedFreshOrdinaryContext InternedGuardedBudget InternedGuardedBudgetProbeHeap InternedGuardedBudgetRequest
open InternedRecordDepthShape (shape)

/-- Actual simultaneous stored substitution has its exact smart-plan budget language and retains both heaps. -/
theorem execute_checked [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (replacements : Environment Symbol Guard) (state : State Symbol Guard) (context : Context state [])
    (heap : Heap state) (depthHeap : InternedFreshOrdinaryDepthHeap.Heap state)
    (available : Available state value) (valid : Replacements state replacements) :
    Checked (InternedFreshOrdinaryStoredSubstitution.execute value replacements state) (fun result => ∀ holds ambient,
      meaning holds ambient result = InternedGuardedSmartBudget.evaluate holds
        (((leaves value).map (input replacements)).map shape)
        (((leaves value).map (input replacements)).map (meaning holds ambient)) (encode (leaves value) [] value)) :=
  InternedGuardedBudgetExecution.build_language (encode (leaves value) [] value) ((leaves value).map (input replacements)) state
    (InternedGuardedStoredExecution.plan_context value replacements state context available valid) heap depthHeap

/-- Actual outer-Mu unfolding has the exact smart language of its compiled replacement plan. -/
theorem unfold_mu_checked [DecidableEq (EdgeKey Symbol Guard)]
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (body depth ordinary : Value Symbol Guard)
    (state : State Symbol Guard) (context : Context state []) (heap : Heap state)
    (depthHeap : InternedFreshOrdinaryDepthHeap.Heap state) (available : Available state (.mu entry body depth ordinary)) :
    let replacements : Environment Symbol Guard := fun name =>
      if name = .interned entry.identity then some (.mu entry body depth ordinary) else none
    Checked (InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary) state) (fun result => ∀ holds ambient,
      meaning holds ambient result = InternedGuardedSmartBudget.evaluate holds
        (((leaves body).map (input replacements)).map shape)
        (((leaves body).map (input replacements)).map (meaning holds ambient)) (encode (leaves body) [] body)) := by
  dsimp only
  apply execute_checked body _ state context heap depthHeap (available.children body (by simp [InternedProbeProvenance.children]))
  intro name replacement found
  dsimp only at found
  split at found
  · cases found; exact available
  · contradiction

/-- Every actual stored outer unfolding retains both complete probe heaps. -/
theorem unfold_heaps [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (state : State Symbol Guard) (context : Context state []) (heap : Heap state)
    (depthHeap : InternedFreshOrdinaryDepthHeap.Heap state) (available : Available state value) :
    Heap (InternedFreshOrdinaryStoredSubstitution.unfold value state).state ∧
      InternedFreshOrdinaryDepthHeap.Heap (InternedFreshOrdinaryStoredSubstitution.unfold value state).state := by
  cases value with
  | empty | reference | node | union => exact ⟨heap, depthHeap⟩
  | mu entry body depth ordinary =>
      have checked := unfold_mu_checked entry body depth ordinary state context heap depthHeap available
      exact ⟨checked.heap, checked.depthHeap⟩

end MicroCFTA.InternedGuardedBudgetStoredExecution
