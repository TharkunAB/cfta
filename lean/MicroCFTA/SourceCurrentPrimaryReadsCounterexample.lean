import MicroCFTA.EndpointMemoGateTrace
import MicroCFTA.SourceEqualityPCSNativeEdge

/-!
# Unanchored ordinary query in the historical primary read receipt

The old endpoint_closed constructor can attach a query for an unrelated
record to a completed resident node trace. The resulting global table
contains a nonresident input. This is a receipt-model counterexample.
It is not a counterexample to the Haskell gate implementation.
-/
namespace MicroCFTA.SourceCurrentPrimaryReadsCounterexample
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => State Symbol Guard
local notation "Node" => Value Symbol Guard
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option cbv.maxSteps 200000000

private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq) (FormulaOrder.formula_eq first second)

private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq

private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)

/-- A closed ordinary root retains one actual recursive child. -/
def expression : Syntax Symbol Guard :=
  .node [.mk ("root", .top) top [.binder true (.node [.mk ("loop", .top) top [.var 0]])]]

def construction : Outcome Symbol Guard Node := InternedFreshOrdinaryConstruction.build expression [] empty
def heap : Heap := construction.state
def value : Node := match construction with | .done result _ => result | .pending .. => .empty
def entry : Interned InternedBinderProtocol.NodeKey := match value with | .node result .. => result | _ => ⟨0, .node []⟩
def edges : List (EdgeValue Symbol Guard) := match value with | .node _ result .. => result | _ => []

/-- The resident trace node comes from the actual completed original constructor run. -/
theorem source_return : construction = .done value heap := by cbv

/-- The ordinary root is closed and has positive cached recursive depth. -/
theorem source_shape : value = .node entry edges 1 [] := by cbv

/-- The actual constructor heap satisfies every gate-ready invariant. -/
theorem ready : InternedFreshOrdinaryMemoGateTrace.Ready heap :=
  InternedFreshOrdinaryMemoGateTrace.node_ready
    (InternedFreshOrdinaryGateRank.fromCompleted expression value heap source_return)

/-- The exact node used by the gate trace is resident and recursively available. -/
theorem available : Available heap (.node entry edges 1 []) :=
  source_shape ▸ (InternedFreshOrdinaryGateRank.fromCompleted expression value heap source_return).available

/-- This different ordinary record was never installed by the constructor run. -/
def unrelated : Node := .node ⟨999, .node []⟩ [] 1 []

/-- The unrelated queried node has no resident record in the actual source heap. -/
theorem unrelated_not_available : ¬ Available heap unrelated := by
  intro present
  have stored := present.resident ⟨999, .node []⟩ rfl
  have absent : heap.nodeRecords (.node []) = none := by cbv
  rw [absent] at stored
  cases stored

def initialMemos : EndpointMemoGateTrace.Memos := ⟨InternedFreshOrdinaryUnfoldMemo.empty, SourceEndpointMemo.empty⟩
noncomputable def savedQuery : SourceEndpointMemo.Memos := (SourceEndpointMemo.run unrelated initialMemos.query).2
noncomputable def finalMemos : EndpointMemoGateTrace.Memos := { initialMemos with query := savedQuery }

/-- All three initial memo families are valid on the actual constructed heap. -/
theorem initial_valid : EndpointMemoGateTrace.Valid heap initialMemos :=
  ⟨InternedFreshOrdinaryUnfoldMemo.empty_correct heap, SourceEndpointMemo.empty_valid heap⟩

/-- The unrelated query is a literal completed memo execution. -/
theorem unrelated_run : SourceEndpointMemo.run unrelated initialMemos.query = (reaches unrelated, savedQuery) := by
  cbv

/-- The gate trace itself queries the actual resident root and leaves the heap unchanged. -/
theorem trace : EndpointStatefulGateTrace.NodeTrace source reaches [] (.node entry edges 1 []) heap
    (!(([] : List InternedBinderProtocol.Reference).isEmpty) || reaches (.node entry edges 1 [])) heap :=
  .endpoint (by decide)

/-- The indexed gate trace has a completed execution with a finite budget. -/
theorem trace_complete : ∃ fuel,
    EndpointStatefulGate.nodeMeets source reaches fuel [] (.node entry edges 1 []) heap =
      .done (some (!(([] : List InternedBinderProtocol.Reference).isEmpty) ||
        reaches (.node entry edges 1 []))) heap :=
  EndpointStatefulGateTrace.node_trace_complete source reaches [] _ heap _ heap trace

/-- The old receipt permits independent queried entry and edges at that same trace index. -/
theorem unanchored_reads : EndpointMemoGateTrace.NodeReads trace initialMemos finalMemos :=
  .endpoint_closed (entry := ⟨999, .node []⟩) (edges := []) (by decide) (by decide) unrelated_run

/-- The returned descendant table literally stores the unrelated nonresident input. -/
theorem stored_unrelated : finalMemos.query.descendants unrelated.referenceOf = some (unrelated, false) := by
  cbv

/-- Valid initial tables and a resident completed trace do not validate this old supplied receipt. -/
theorem final_invalid : ¬ EndpointMemoGateTrace.Valid heap finalMemos := by
  intro valid
  exact unrelated_not_available (valid.query.descendants _ _ _ stored_unrelated).2.1

/-- The counterexample includes actual construction, gate readiness, availability, and completed reads. -/
theorem counterexample : construction = .done value heap ∧ InternedFreshOrdinaryMemoGateTrace.Ready heap ∧
    Available heap (.node entry edges 1 []) ∧ EndpointMemoGateTrace.Valid heap initialMemos ∧
    EndpointMemoGateTrace.NodeReads trace initialMemos finalMemos ∧ ¬ EndpointMemoGateTrace.Valid heap finalMemos :=
  ⟨source_return, ready, available, initial_valid, unanchored_reads, final_invalid⟩

/-- The invalid receipt can accompany an actual completed gate execution. -/
theorem execution_counterexample : ∃ fuel,
    EndpointStatefulGate.nodeMeets source reaches fuel [] (.node entry edges 1 []) heap =
      .done (some (!(([] : List InternedBinderProtocol.Reference).isEmpty) ||
        reaches (.node entry edges 1 []))) heap ∧
    InternedFreshOrdinaryMemoGateTrace.Ready heap ∧ Available heap (.node entry edges 1 []) ∧
    EndpointMemoGateTrace.Valid heap initialMemos ∧
    EndpointMemoGateTrace.NodeReads trace initialMemos finalMemos ∧
    ¬ EndpointMemoGateTrace.Valid heap finalMemos := by
  obtain ⟨fuel, done⟩ := trace_complete
  exact ⟨fuel, done, ready, available, initial_valid, unanchored_reads, final_invalid⟩

end MicroCFTA.SourceCurrentPrimaryReadsCounterexample
