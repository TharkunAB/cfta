import MicroCFTA.SourceEqualityPhysicalPayload
import MicroCFTA.SourceEqualityOnePassAPI

/-!
# Actual guarded-edge reconstruction after a native equality pass

The source accessor supplies the physical own payload. The complete pass
runs on the original children. Literal makeEdge retains the original symbol
and full constraint and advances the same warm native state.
-/
namespace MicroCFTA.SourceEqualityGuardedEdgeGraph
open InternedConstructorTemplates SourceObservations SourceSymbolicIndex
open SourceEqualityClassFoldGraph SourceEqualityNativeScoped
variable {Formula : Type}
local notation "Symbol" => Label Formula
local notation "Guard" => Constraint Formula

/-- A complete source edge pass retains actual payload readback, native processing, and literal interning. -/
inductive Graph [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (edge : EdgeValue Symbol Guard) (inherited : SourceEqualityPrecheck.Constraint) (before : NativeState width Symbol Guard) :
    EdgeValue Symbol Guard → NativeState width Symbol Guard → Prop where
  | done {payload results middle}
      (physical : SourceEqualityPhysicalPayload.own edge.entry.key.constraint = .ok payload)
      (pass : SourceEqualityOnePassGraph.Execution unconstrained emptyGuard conjoin clear top payload inherited edge.children before (.ok results) middle) :
      Graph unconstrained emptyGuard conjoin clear top edge inherited before
        (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint results) middle.machine.heap).1
        (advanceHeap middle (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint results) middle.machine.heap).2)

/-- Range checks concern only the actual physical payload and the reached native requests. -/
def Ranges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (edge : EdgeValue Symbol Guard) (inherited : SourceEqualityPrecheck.Constraint) (before : NativeState width Symbol Guard) : Prop :=
  ∀ payload, SourceEqualityPhysicalPayload.own edge.entry.key.constraint = .ok payload →
    SourceEqualityOnePassGraph.Ranges unconstrained emptyGuard conjoin clear top
      (SourceEqualityPrecheck.precheck payload inherited) edge.children before

end MicroCFTA.SourceEqualityGuardedEdgeGraph
