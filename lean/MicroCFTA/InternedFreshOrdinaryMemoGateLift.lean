import MicroCFTA.InternedFreshOrdinaryMemoGateTrace

/-!
# Coherent unfolding memo composition through complete gate graphs

Every source node, child, and ordered edge graph has an actual memo trace.
The proof derives each memo hit or miss from its coherent current cache.
Both caches and all semantic invariants pass to each later query.
-/
namespace MicroCFTA.InternedFreshOrdinaryMemoGateTrace
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedFreshOrdinaryGateRank (Node)
open InternedFreshOrdinaryUnfoldMemo (Memo Correct)
open EqualityNormalize

/-- Every complete source node graph lifts to actual coherent memo execution with exact constructor readback. -/
theorem lift_node [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (path : Path) (value : Value Symbol Guard) (state : State Symbol Guard) (answer : Bool) (final : State Symbol Guard)
    (trace : InternedFreshOrdinaryStatefulGateTrace.NodeTrace unconstrained path value state answer final)
    (ready : Ready state) (available : Available state value) (memo : Memo Symbol Guard) (correct : Correct state memo) :
    ∃ saved, NodeTrace unconstrained path value memo state answer saved final ∧ Keeps state final saved := by
  revert correct memo available ready
  induction trace using InternedFreshOrdinaryStatefulGateTrace.NodeTrace.rec
      (motive_2 := fun values index path state answer final _ => Ready state →
        (∀ value ∈ values, Available state value) → ∀ memo, Correct state memo →
          ∃ saved, ChildTrace unconstrained values index path memo state answer saved final ∧ Keeps state final saved)
      (motive_3 := fun index path edges state answer final _ => Ready state →
        (∀ value ∈ edges.flatMap EdgeValue.children, Available state value) → ∀ memo, Correct state memo →
          ∃ saved, EdgesTrace unconstrained index path edges memo state answer saved final ∧ Keeps state final saved) with
  | empty => intro ready available memo correct; exact ⟨memo, .empty, pure_keeps _ memo ready correct⟩
  | reference => intro ready available memo correct; exact ⟨memo, .reference, pure_keeps _ memo ready correct⟩
  | union members => intro ready available memo correct; exact ⟨memo, .union members, pure_keeps _ memo ready correct⟩
  | finite fast => intro ready available memo correct; exact ⟨memo, .finite fast, pure_keeps _ memo ready correct⟩
  | endpoint slow => intro ready available memo correct; exact ⟨memo, .endpoint slow, pure_keeps _ memo ready correct⟩
  | branches slow trace ih =>
      intro ready available memo correct
      obtain ⟨saved, actual, kept⟩ := ih ready (fun value member => available.children value member) memo correct
      exact ⟨saved, .branches slow actual, kept⟩
  | constrained blocked => intro ready available memo correct; exact ⟨memo, .constrained blocked, pure_keeps _ memo ready correct⟩
  | closed plain closed => intro ready available memo correct; exact ⟨memo, .closed plain closed, pure_keeps _ memo ready correct⟩
  | unfold plain opened actual trace ih =>
      intro ready available memo correct
      obtain ⟨after, afterMemo, memoActual, readback, afterCorrect, growth, history⟩ :=
        InternedFreshOrdinaryUnfoldMemo.run_complete (ready.node _ available) memo correct
      have fields := Outcome.done.inj (readback.symm.trans actual)
      have valueEqual := fields.1
      have stateEqual := fields.2
      have afterReady := stateEqual ▸ node_ready after
      have afterAvailable := stateEqual ▸ (valueEqual ▸ after.available)
      have memoCorrect := stateEqual ▸ afterCorrect
      obtain ⟨saved, next, kept⟩ := ih afterReady afterAvailable afterMemo memoCorrect
      refine ⟨saved, .unfold plain opened ?_ actual next, prepend_keeps (firstMemo := afterMemo) ?_ kept⟩
      · simpa only [Ready.node, valueEqual, stateEqual] using memoActual
      · exact ⟨afterReady, memoCorrect, by simpa only [Ready.node, stateEqual] using growth, by simpa only [Ready.node, stateEqual] using history⟩
  | missing absent ready available memo correct => exact ⟨memo, .missing absent, pure_keeps _ memo ready correct⟩
  | present found trace ih ready available memo correct =>
      obtain ⟨saved, actual, kept⟩ := ih ready (available _ (List.mem_of_getElem? found)) memo correct
      exact ⟨saved, .present found actual, kept⟩
  | nil ready available memo correct => exact ⟨memo, .nil, pure_keeps _ memo ready correct⟩
  | stop head ih ready available memo correct =>
      obtain ⟨saved, actual, kept⟩ := ih ready (fun value member => available value (by simp [member])) memo correct
      exact ⟨saved, .stop actual, kept⟩
  | next head tail headIH tailIH ready available memo correct =>
      obtain ⟨middleMemo, first, firstKept⟩ := headIH ready (fun value member => available value (by simp [member])) memo correct
      obtain ⟨saved, rest, restKept⟩ := tailIH firstKept.ready
        (fun value member => (available value (by simp [member])).grows _ _ firstKept.growth firstKept.history)
        middleMemo firstKept.correct
      exact ⟨saved, .next first rest, prepend_keeps firstKept restKept⟩

end MicroCFTA.InternedFreshOrdinaryMemoGateTrace
