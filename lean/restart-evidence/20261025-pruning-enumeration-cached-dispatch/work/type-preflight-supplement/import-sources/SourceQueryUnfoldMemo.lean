import MicroCFTA.EndpointMemoGateTrace
import MicroCFTA.SourceEqualityOpenOrdinaryHead
import MicroCFTA.InternedFreshOrdinaryStoredCosts

/-!
# Completed unfolding memo receipts for source queries

An actual unfolding determines the output and constructor heap of its memo
call. A hit retains the memo. A miss inserts only at an absent key. Earlier
entries therefore remain unchanged. Constructor growth also retains the
coherence of all three current gate tables. It does not describe helper-call
absence or runtime publication.
-/
namespace MicroCFTA.SourceQueryUnfoldMemo
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open InternedFreshOrdinaryUnfoldMemo (Memo Correct)

/-- Insertion at an absent physical key preserves every earlier unfolding entry. -/
theorem insert_extends (memo : Memo Symbol Guard) (input output : Value Symbol Guard)
    (absent : memo input.referenceOf = none) :
    Extends memo (InternedFreshOrdinaryUnfoldMemo.insert memo input output) := by
  intro key original found
  simp only [InternedFreshOrdinaryUnfoldMemo.insert]
  split
  · rename_i same
    subst key
    rw [absent] at found
    cases found
  · exact found

/-- Every completed actual unfolding-memo call preserves all earlier entries. -/
theorem run_extends [DecidableEq (EdgeKey Symbol Guard)] (input output : Value Symbol Guard)
    (memo saved : Memo Symbol Guard) (before after : State Symbol Guard)
    (actual : InternedFreshOrdinaryUnfoldMemo.run input memo before = .done (output, saved) after) :
    Extends memo saved := by
  cases found : memo input.referenceOf with
  | some pair =>
      simp only [InternedFreshOrdinaryUnfoldMemo.run, found, Outcome.done.injEq, Prod.mk.injEq] at actual
      rcases actual with ⟨⟨_, rfl⟩, _⟩
      exact extends_refl memo
  | none =>
      cases unfolded : InternedFreshOrdinaryStoredSubstitution.unfold input before with
      | pending key current =>
          simp only [InternedFreshOrdinaryUnfoldMemo.run, found, unfolded, Outcome.bind] at actual
          cases actual
      | done value current =>
          simp only [InternedFreshOrdinaryUnfoldMemo.run, found, unfolded, Outcome.bind,
            Outcome.done.injEq, Prod.mk.injEq] at actual
          rcases actual with ⟨⟨_, same⟩, _⟩
          rw [← same]
          exact insert_extends memo input value found

/-- An actual completed unfolding derives the identical memo output, heap, and retained entries. -/
theorem run_of_unfold [DecidableEq (EdgeKey Symbol Guard)] (input output : Value Symbol Guard)
    (before after : State Symbol Guard)
    (actual : InternedFreshOrdinaryStoredSubstitution.unfold input before = .done output after)
    (semantic : SemanticReady before) (costs : InternedFreshOrdinaryCostHeap.Heap before)
    (available : Available before input) (memo : Memo Symbol Guard) (correct : Correct before memo) :
    ∃ saved : Memo Symbol Guard,
      InternedFreshOrdinaryUnfoldMemo.run input memo before = .done (output, saved) after ∧
      Correct after saved ∧ Extends memo saved ∧ Grows before after ∧
      Extends before.nodes.issued after.nodes.issued := by
  let ready : InternedFreshOrdinaryMemoGateTrace.Ready before :=
    ⟨semantic.ready.semantic.1, semantic.ready.semantic.2, semantic.ready.covered, costs⟩
  let node := ready.node input available
  obtain ⟨finished, saved, executed, readback, retained, growth, history⟩ :=
    InternedFreshOrdinaryUnfoldMemo.run_complete node memo correct
  dsimp only [node, InternedFreshOrdinaryMemoGateTrace.Ready.node] at executed readback growth history
  have same := Outcome.done.inj (readback.symm.trans actual)
  have receipt : InternedFreshOrdinaryUnfoldMemo.run input memo before = .done (output, saved) after := by
    simpa only [same.1, same.2] using executed
  refine ⟨saved, receipt, ?_, run_extends input output memo saved before after receipt, ?_, ?_⟩
  · simpa only [same.2] using retained
  · simpa only [same.2] using growth
  · simpa only [same.2] using history

open SourceObservations SourceSymbolicIndex
local notation "SourceSymbol" => Label FullSyntax.Formula
local notation "SourceGuard" => Constraint FullSyntax.Formula

/-- Actual constructor effects retain coherence of the same three completed source tables. -/
theorem valid_grows [DecidableEq (EdgeKey SourceSymbol SourceGuard)]
    (before after : State SourceSymbol SourceGuard) (semantic : SemanticReady before)
    (keeps : SourceEqualityRequiredCache.Keeps before after) (memos : EndpointMemoGateTrace.Memos)
    (valid : EndpointMemoGateTrace.Valid before memos) : EndpointMemoGateTrace.Valid after memos := by
  exact ⟨InternedFreshOrdinaryUnfoldMemo.grows before after semantic.ready.semantic.1.normal.facts.coherent.valid
      keeps.growth keeps.history memos.unfolding valid.unfolding,
    SourceEndpointMemo.grows before after keeps.growth keeps.history memos.query valid.query⟩

/-- An actual source unfolding updates only its unfolding table and derives all returned memo coherence. -/
theorem run_memos_of_unfold [DecidableEq (EdgeKey SourceSymbol SourceGuard)]
    (input output : Value SourceSymbol SourceGuard) (before after : State SourceSymbol SourceGuard)
    (actual : InternedFreshOrdinaryStoredSubstitution.unfold input before = .done output after)
    (semantic : SemanticReady before) (costs : InternedFreshOrdinaryCostHeap.Heap before)
    (available : Available before input) (memos : EndpointMemoGateTrace.Memos)
    (valid : EndpointMemoGateTrace.Valid before memos) :
    ∃ saved : EndpointMemoGateTrace.Memos,
      InternedFreshOrdinaryUnfoldMemo.run input memos.unfolding before = .done (output, saved.unfolding) after ∧
      saved.query = memos.query ∧ EndpointMemoGateTrace.Valid after saved ∧
      Extends memos.unfolding saved.unfolding := by
  obtain ⟨saved, receipt, coherent, retained, growth, history⟩ :=
    run_of_unfold input output before after actual semantic costs available memos.unfolding valid.unfolding
  exact ⟨{memos with unfolding := saved}, receipt, rfl,
    ⟨coherent, SourceEndpointMemo.grows before after growth history memos.query valid.query⟩, retained⟩

end MicroCFTA.SourceQueryUnfoldMemo
