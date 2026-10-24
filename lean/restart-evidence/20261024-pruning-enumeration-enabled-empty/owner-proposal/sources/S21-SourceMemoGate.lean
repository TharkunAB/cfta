import MicroCFTA.InternedFreshOrdinaryMemoGateClasses
import MicroCFTA.InternedSourceCrushInventory
import MicroCFTA.SourceCyclicAutomaton
import MicroCFTA.SolverAdapter

/-!
# Source constraint reads in the complete memo gate

The gate predicate is the actual visited-node Boolean crush. Each ordinary
edge uses the existing normalized equality and residual source test. Original
construction derives complete memo traces with this concrete node read.
-/
namespace MicroCFTA.SourceMemoGate
open InternedConstructorTemplates InternedNestedConstruction
open InternedProbeProvenance InternedRecordCoherence
open SourceObservations SourceSymbolicIndex SourceGuards
open InternedFreshOrdinaryGateRank (Node)
open InternedFreshOrdinaryMemoGateTrace (Keeps NodeTrace ClassTrace)

local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula

/-- The source edge test requires empty normalized equalities and no residual guard. -/
noncomputable def plain (constraint : Guard) : Bool :=
  decide (SourceCompactGuards.sourceEqualities constraint = some []) &&
    (SourceCompactGuards.positiveNormalized constraint.guard).isSome

/-- The concrete edge read is exactly the source test already used by cyclic import. -/
theorem plain_eq {Key : Type} (edge : SourceCyclicAutomaton.Row Key FullSyntax.Formula) :
    plain edge.constraint = SourceCyclicAutomaton.unconstrained edge := rfl

/-- The complete source node read executes the actual visited-node crush from an empty visited set. -/
noncomputable def unconstrained (value : Value Symbol Guard) : Bool := InternedSourceCrush.unconstrained plain value

/-- Actual source predicate traversal visits distinct identities bounded by the current reservation counter. -/
theorem predicate_inventory (value : Value Symbol Guard) (state : State Symbol Guard)
    (coherent : Coherent state) (available : Available state value) :
    (InternedSourceCrush.visit plain value []).2.Nodup ∧
      (InternedSourceCrush.visit plain value []).2.length ≤ state.nodes.next :=
  InternedSourceCrush.empty_inventory_bound plain value state coherent available

/-- Original source construction derives complete memo node graphs with the concrete source predicate. -/
theorem nodes [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) :
    ∃ value state, ∃ _done : InternedFreshOrdinaryConstruction.build expression [] empty = .done value state,
      ∀ path, ∃ bound answer, ∃ after : Node Symbol Guard, ∃ saved,
        NodeTrace unconstrained path value InternedFreshOrdinaryUnfoldMemo.empty state answer saved after.state ∧
        Keeps state after.state saved ∧
        ∀ extra, InternedFreshOrdinaryStatefulGate.nodeMeets unconstrained (bound + extra) path value state =
          .done (some answer) after.state :=
  InternedFreshOrdinaryMemoGateTrace.source_nodes expression unconstrained

/-- Every original outgoing edge has complete memo class graphs with no supplied node-predicate law. -/
theorem classes [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) :
    ∃ value state, ∃ _done : InternedFreshOrdinaryConstruction.build expression [] empty = .done value state,
      ∀ entry edges depth free, value = .node entry edges depth free → ∀ edge ∈ edges, ∀ paths,
        ∃ bound answer, ∃ after : Node Symbol Guard, ∃ saved,
          ClassTrace unconstrained edge.children paths InternedFreshOrdinaryUnfoldMemo.empty state answer saved after.state ∧
          Keeps state after.state saved ∧
          ∀ extra, InternedFreshOrdinaryStatefulGate.classMeets unconstrained (bound + extra) edge.children paths state =
            .done (some answer) after.state :=
  InternedFreshOrdinaryMemoGateTrace.source_classes expression unconstrained

end MicroCFTA.SourceMemoGate
