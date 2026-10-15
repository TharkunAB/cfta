import MicroCFTA.SourceMemoClassSelection
import MicroCFTA.SourceClosedGateCache

/-!
# Both source memo receipts on closed available gate inputs

A closed gate call cannot enter the open-binder unfolding branch. Its
unfolding memo therefore stays unchanged. Every binder still executes the
actual predicate memo lookup or insertion. Physical record facts suffice;
no unfolding cost heap or original-construction history is an input.
-/
namespace MicroCFTA.SourceClosedGateMemoNodes
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceObservations SourceSymbolicIndex EqualityNormalize
open SourceUnconstrainedMemo (Memo Correct)
open InternedFreshOrdinaryStatefulGateTrace
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "UMemo" => InternedFreshOrdinaryUnfoldMemo.Memo Symbol Guard
local notation "source" => SourceMemoGate.unconstrained
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Actual closed node traces retain an unchanged unfolding memo and every concrete predicate memo call. -/
theorem node {path value before answer after} (trace : NodeTrace source path value before answer after) :
    Facts before → Available before value → value.free = [] → ∀ (unfolding : UMemo) (predicate : Memo), Correct before predicate →
      ∃ saved, ∃ receipt : InternedFreshOrdinaryMemoGateTrace.NodeTrace source path value unfolding before answer unfolding after,
        SourcePredicateGateTrace.NodeReads receipt predicate saved ∧ Correct after saved := by
  induction trace using NodeTrace.rec
      (motive_2 := fun values index path before answer after _ =>
        Facts before → Values before values → ClosedValues values → ∀ (unfolding : UMemo) (predicate : Memo), Correct before predicate →
          ∃ saved, ∃ receipt : InternedFreshOrdinaryMemoGateTrace.ChildTrace source values index path unfolding before answer unfolding after,
            SourcePredicateGateTrace.ChildReads receipt predicate saved ∧ Correct after saved)
      (motive_3 := fun index path edges before answer after _ =>
        Facts before → Edges before edges → ClosedEdges edges → ∀ (unfolding : UMemo) (predicate : Memo), Correct before predicate →
          ∃ saved, ∃ receipt : InternedFreshOrdinaryMemoGateTrace.EdgesTrace source index path edges unfolding before answer unfolding after,
            SourcePredicateGateTrace.EdgesReads receipt predicate saved ∧ Correct after saved) with
  | empty => intro _ _ _ _ predicate correct; exact ⟨predicate, .empty, .empty, correct⟩
  | reference => intro _ _ _ _ predicate correct; exact ⟨predicate, .reference, .reference, correct⟩
  | union members => intro _ _ _ _ predicate correct; exact ⟨predicate, .union members, .union members, correct⟩
  | finite fast => intro _ _ _ _ predicate correct; exact ⟨predicate, .finite fast, .finite fast, correct⟩
  | endpoint slow => intro _ _ _ _ predicate correct; exact ⟨predicate, .endpoint slow, .endpoint slow, correct⟩
  | branches slow trace ih =>
      intro facts available closed unfolding predicate correct
      obtain ⟨saved, receipt, reads, kept⟩ := ih facts
        (InternedEdgeResidency.resident_edges _ facts.linked _ available.resident)
        (MergedColdReaderClosed.node_children_closed _ facts _ _ _ _ available closed) unfolding predicate correct
      exact ⟨saved, .branches slow receipt, .branches slow reads, kept⟩
  | constrained blocked =>
      intro facts available _ unfolding predicate correct
      have checked := SourceUnconstrainedMemo.run_exact _ _ facts.coherent available predicate correct
      have actual : SourceUnconstrainedMemo.run _ predicate = (false, (SourceUnconstrainedMemo.run _ predicate).2) :=
        Prod.ext (checked.1.trans blocked) rfl
      exact ⟨_, .constrained blocked, .constrained blocked actual, checked.2⟩
  | closed plain shut =>
      intro facts available _ unfolding predicate correct
      have checked := SourceUnconstrainedMemo.run_exact _ _ facts.coherent available predicate correct
      have actual : SourceUnconstrainedMemo.run _ predicate = (true, (SourceUnconstrainedMemo.run _ predicate).2) :=
        Prod.ext (checked.1.trans plain) rfl
      exact ⟨_, .closed plain shut, .closed plain shut actual, checked.2⟩
  | unfold plain opened actual trace ih =>
      intro _ _ closed
      simp only [closed, List.isEmpty_nil] at opened
      cases opened
  | missing absent _ _ _ _ predicate correct => exact ⟨predicate, .missing absent, .missing absent, correct⟩
  | present found trace ih facts available closed unfolding predicate correct =>
      have member := List.mem_of_getElem? found
      obtain ⟨saved, receipt, reads, kept⟩ := ih facts (available _ member) (closed _ member) unfolding predicate correct
      exact ⟨saved, .present found receipt, .present found reads, kept⟩
  | nil _ _ _ _ predicate correct => exact ⟨predicate, .nil, .nil, correct⟩
  | stop head ih facts resident closed unfolding predicate correct =>
      obtain ⟨saved, receipt, reads, kept⟩ := ih facts
        (facts.cached.edges _ _ (resident _ List.mem_cons_self)) (closed _ List.mem_cons_self) unfolding predicate correct
      exact ⟨saved, .stop receipt, .stop reads, kept⟩
  | next head tail headIH tailIH facts resident closed unfolding predicate correct =>
      have available := facts.cached.edges _ _ (resident _ List.mem_cons_self)
      have childClosed := closed _ List.mem_cons_self
      obtain ⟨middlePredicate, first, firstReads, firstCorrect⟩ := headIH facts available childClosed unfolding predicate correct
      have same := SourceClosedGateCache.child_state head facts available childClosed
      cases same
      obtain ⟨saved, rest, restReads, restCorrect⟩ := tailIH facts
        (fun edge member => resident edge (List.mem_cons_of_mem _ member))
        (fun edge member => closed edge (List.mem_cons_of_mem _ member)) unfolding middlePredicate firstCorrect
      exact ⟨saved, .next first rest, .next firstReads restReads, restCorrect⟩

end MicroCFTA.SourceClosedGateMemoNodes
