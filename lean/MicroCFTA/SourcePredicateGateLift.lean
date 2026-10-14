import MicroCFTA.SourcePredicateGateTrace

/-!
# Coherent predicate memo composition through complete source graphs

Every existing unfolding memo graph receives actual predicate memo receipts.
Canonical coherence gives each read. Constructor growth preserves earlier
reads before the next node, edge, or path query.
-/
namespace MicroCFTA.SourcePredicateGateTrace
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open SourceObservations SourceSymbolicIndex EqualityNormalize
open SourceUnconstrainedMemo (Memo Correct run)
open InternedFreshOrdinaryMemoGateTrace (Ready node_ready)

local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "UMemo" => InternedFreshOrdinaryUnfoldMemo.Memo Symbol Guard
local notation "source" => SourceMemoGate.unconstrained

/-- Every complete unfolding memo graph carries the actual coherent predicate memo through all ordered queries. -/
theorem lift_node [DecidableEq (EdgeKey Symbol Guard)]
    (path : Path) (value : Value Symbol Guard) (memo : UMemo) (state : State Symbol Guard)
    (answer : Bool) (saved : UMemo) (final : State Symbol Guard)
    (trace : InternedFreshOrdinaryMemoGateTrace.NodeTrace source path value memo state answer saved final)
    (ready : Ready state) (available : Available state value)
    (unfoldCorrect : InternedFreshOrdinaryUnfoldMemo.Correct state memo) (predicate : Memo) (correct : Correct state predicate) :
    ∃ savedPredicate, NodeReads trace predicate savedPredicate ∧ Keeps state final saved savedPredicate := by
  revert correct predicate unfoldCorrect available ready
  induction trace using InternedFreshOrdinaryMemoGateTrace.NodeTrace.rec
      (motive_2 := fun values index path memo state answer saved final trace => Ready state →
        (∀ value ∈ values, Available state value) → InternedFreshOrdinaryUnfoldMemo.Correct state memo →
          ∀ predicate, Correct state predicate →
            ∃ savedPredicate, ChildReads trace predicate savedPredicate ∧ Keeps state final saved savedPredicate)
      (motive_3 := fun index path edges memo state answer saved final trace => Ready state →
        (∀ value ∈ edges.flatMap EdgeValue.children, Available state value) → InternedFreshOrdinaryUnfoldMemo.Correct state memo →
          ∀ predicate, Correct state predicate →
            ∃ savedPredicate, EdgesReads trace predicate savedPredicate ∧ Keeps state final saved savedPredicate) with
  | empty => intro ready available unfoldCorrect predicate correct; exact ⟨predicate, .empty, pure_keeps _ _ _ ready unfoldCorrect correct⟩
  | reference => intro ready available unfoldCorrect predicate correct; exact ⟨predicate, .reference, pure_keeps _ _ _ ready unfoldCorrect correct⟩
  | union members => intro ready available unfoldCorrect predicate correct; exact ⟨predicate, .union members, pure_keeps _ _ _ ready unfoldCorrect correct⟩
  | finite fast => intro ready available unfoldCorrect predicate correct; exact ⟨predicate, .finite fast, pure_keeps _ _ _ ready unfoldCorrect correct⟩
  | endpoint slow => intro ready available unfoldCorrect predicate correct; exact ⟨predicate, .endpoint slow, pure_keeps _ _ _ ready unfoldCorrect correct⟩
  | branches slow trace ih =>
      intro ready available unfoldCorrect predicate correct
      obtain ⟨savedPredicate, actual, kept⟩ := ih ready (fun value member => available.children value member) unfoldCorrect predicate correct
      exact ⟨savedPredicate, .branches slow actual, kept⟩
  | constrained blocked =>
      intro ready available unfoldCorrect predicate correct
      have checked := SourceUnconstrainedMemo.run_exact _ _ ready.1.normal.facts.coherent available predicate correct
      have actual : run _ predicate = (false, (run _ predicate).2) := Prod.ext (checked.1.trans blocked) rfl
      exact ⟨_, .constrained blocked actual, pure_keeps _ _ _ ready unfoldCorrect checked.2⟩
  | closed plain closed =>
      intro ready available unfoldCorrect predicate correct
      have checked := SourceUnconstrainedMemo.run_exact _ _ ready.1.normal.facts.coherent available predicate correct
      have actual : run _ predicate = (true, (run _ predicate).2) := Prod.ext (checked.1.trans plain) rfl
      exact ⟨_, .closed plain closed actual, pure_keeps _ _ _ ready unfoldCorrect checked.2⟩
  | unfold plain opened actual readback trace ih =>
      intro ready available unfoldCorrect predicate correct
      have checked := SourceUnconstrainedMemo.run_exact _ _ ready.1.normal.facts.coherent available predicate correct
      have query : run _ predicate = (true, (run _ predicate).2) := Prod.ext (checked.1.trans plain) rfl
      obtain ⟨after, afterMemo, memoActual, _, afterCorrect, growth, history⟩ :=
        InternedFreshOrdinaryUnfoldMemo.run_complete (ready.node _ available) _ unfoldCorrect
      have fields := Outcome.done.inj (memoActual.symm.trans actual)
      have valueEqual := congrArg Prod.fst fields.1
      have memoEqual := congrArg Prod.snd fields.1
      dsimp only at valueEqual memoEqual
      have stateEqual := fields.2
      have afterReady := stateEqual ▸ node_ready after
      have afterAvailable := stateEqual ▸ (valueEqual ▸ after.available)
      have memoCorrect := stateEqual ▸ (memoEqual ▸ afterCorrect)
      have predicateCorrect := stateEqual ▸ SourceUnconstrainedMemo.grows _ _ growth history _ checked.2
      obtain ⟨savedPredicate, next, kept⟩ := ih afterReady afterAvailable memoCorrect _ predicateCorrect
      have firstKept : InternedFreshOrdinaryMemoGateTrace.Keeps _ _ _ :=
        ⟨afterReady, memoCorrect, by simpa only [Ready.node, stateEqual] using growth,
          by simpa only [Ready.node, stateEqual] using history⟩
      exact ⟨savedPredicate, .unfold plain opened actual readback query next, prepend_keeps ⟨firstKept, predicateCorrect⟩ kept⟩
  | missing absent ready available unfoldCorrect predicate correct =>
      exact ⟨predicate, .missing absent, pure_keeps _ _ _ ready unfoldCorrect correct⟩
  | present found trace ih ready available unfoldCorrect predicate correct =>
      obtain ⟨savedPredicate, actual, kept⟩ := ih ready (available _ (List.mem_of_getElem? found)) unfoldCorrect predicate correct
      exact ⟨savedPredicate, .present found actual, kept⟩
  | nil ready available unfoldCorrect predicate correct =>
      exact ⟨predicate, .nil, pure_keeps _ _ _ ready unfoldCorrect correct⟩
  | stop head ih ready available unfoldCorrect predicate correct =>
      obtain ⟨savedPredicate, actual, kept⟩ := ih ready (fun value member => available value (by simp [member])) unfoldCorrect predicate correct
      exact ⟨savedPredicate, .stop actual, kept⟩
  | next head tail headIH tailIH ready available unfoldCorrect predicate correct =>
      obtain ⟨middlePredicate, first, firstKept⟩ := headIH ready
        (fun value member => available value (by simp [member])) unfoldCorrect predicate correct
      obtain ⟨savedPredicate, rest, restKept⟩ := tailIH firstKept.unfolding.ready
        (fun value member => (available value (by simp [member])).grows _ _ firstKept.unfolding.growth firstKept.unfolding.history)
        firstKept.unfolding.correct middlePredicate firstKept.predicate
      exact ⟨savedPredicate, .next first rest, prepend_keeps firstKept restKept⟩

end MicroCFTA.SourcePredicateGateTrace
