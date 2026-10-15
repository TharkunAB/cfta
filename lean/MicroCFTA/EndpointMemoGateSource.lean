import MicroCFTA.EndpointMemoGateLift
import MicroCFTA.EndpointStatefulGateCompletion

/-!
# Original source construction with three completed gate memos

The source constructor run derives the initial resident inputs and heap
invariants. Current-policy finite execution then supplies the logical trace.
That trace derives actual completed calls of all three memo families.
Native table and lazy ownership correspondence remain separate obligations.
-/
namespace MicroCFTA.EndpointMemoGateTrace
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open SourceObservations SourceSymbolicIndex EqualityNormalize
open InternedFreshOrdinaryGateRank (Node fromCompleted)
open InternedFreshOrdinaryMemoGateTrace (node_ready)
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source

/-- All three current gate memo families start without completed entries. -/
def empty : Memos := ⟨InternedFreshOrdinaryUnfoldMemo.empty, SourceEndpointMemo.empty⟩

/-- Empty gate memos are coherent in every physical source heap. -/
theorem empty_valid [DecidableEq (EdgeKey Symbol Guard)] (heap : State Symbol Guard) : Valid heap empty :=
  ⟨InternedFreshOrdinaryUnfoldMemo.empty_correct heap, SourceEndpointMemo.empty_valid heap⟩

/-- Original source construction derives finite current-policy checks and all three returned memo receipts. -/
theorem source_nodes [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) :
    ∃ value heap, ∃ _done : InternedFreshOrdinaryConstruction.build expression [] InternedConstructorTemplates.empty = .done value heap,
      ∀ path, ∃ bound answer, ∃ after : Node Symbol Guard,
        ∃ trace : EndpointStatefulGateTrace.NodeTrace source reaches path value heap answer after.state,
          ∃ saved, NodeReads trace empty saved ∧ Keeps heap after.state saved ∧
            ∀ extra, EndpointStatefulGate.nodeMeets source reaches (bound + extra) path value heap =
              .done (some answer) after.state := by
  obtain ⟨value, heap, done, paths⟩ := EndpointStatefulGateCompletion.source_node_trace expression source reaches
  refine ⟨value, heap, done, ?_⟩
  intro path
  obtain ⟨bound, answer, after, trace, _, _, stable⟩ := paths path
  let original := fromCompleted expression value heap done
  obtain ⟨saved, reads, kept⟩ := lift_node path value heap answer after.state trace
    (node_ready original) original.available empty (empty_valid heap)
  exact ⟨bound, answer, after, trace, saved, reads, kept, stable⟩

end MicroCFTA.EndpointMemoGateTrace
