import MicroCFTA.SourceCurrentStoredRebindBoundary

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.proofs.threshold 254
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000

namespace MicroCFTA.StoredRebindBoundaryChecks
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction
open InternedBinderProtocol (NodeKey)

private def source : Syntax Nat Bool :=
  .binder false (.node [.mk 0 false [.var 0, .binder false (.node [.mk 1 true [.var 1]])]])

private def built := build source [] empty
private def root : Value Nat Bool := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state

private def fields : Value Nat Bool → Interned NodeKey × Value Nat Bool × Value Nat Bool × Value Nat Bool
  | .mu entry body depth ordinary => (entry, body, depth, ordinary)
  | _ => (⟨0, .node []⟩, .empty, .empty, .empty)

private def entry := (fields root).1
private def body := (fields root).2.1
private def depth := (fields root).2.2.1
private def ordinary := (fields root).2.2.2
private def own : InternedBinderProtocol.Reference := .interned entry.identity
private def argument : InternedBinderProtocol.Reference := .uninterned (ordinaryLevel depth)
private def rebound := InternedFreshOrdinaryStoredSubstitution.execute body
  (InternedStoredSubstitutionRebind.replacement own (.reference argument)) heap
private def result : Value Nat Bool := match rebound with | .done value _ => value | .pending .. => .empty
private def after := rebound.state
private def secondChild (value : Value Nat Bool) : Value Nat Bool :=
  ((children value)[1]?).getD .empty

private theorem actual : built = .done root heap := by cbv
private theorem root_shape : root = .mu entry body depth ordinary := by cbv
private theorem rebound_done : rebound = .done result after := by cbv


private def firstRow (value : Value Nat Bool) : EdgeValue Nat Bool :=
  match InternedEdgeResidency.nodeEdges value with
  | row :: _ => row
  | [] => .mk ⟨0, ⟨0, [], false⟩⟩ []

/-- The same finite source retains root payload and child order, while the unequal child agrees after its actual Mu unfold. -/
theorem actual_rows :
    built = .done root heap ∧ rebound = .done result after ∧
    ∃ originalRow rebuiltRow,
      InternedEdgeResidency.nodeEdges ordinary = [originalRow] ∧
      InternedEdgeResidency.nodeEdges result = [rebuiltRow] ∧
      originalRow.entry.key.symbol = 0 ∧ rebuiltRow.entry.key.symbol = 0 ∧
      originalRow.entry.key.constraint = false ∧ rebuiltRow.entry.key.constraint = false ∧
      originalRow.children.length = 2 ∧ rebuiltRow.children.length = 2 ∧
      originalRow.children[0]? = some (.reference argument) ∧
      rebuiltRow.children[0]? = some (.reference argument) ∧
      InternedFreshOrdinaryStoredSubstitution.unfold (secondChild ordinary) after =
        .done (secondChild result) after := by
  refine ⟨actual, rebound_done, firstRow ordinary, firstRow result, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> cbv

end MicroCFTA.StoredRebindBoundaryChecks
#check @MicroCFTA.StoredRebindBoundaryChecks.actual_rows
#print axioms MicroCFTA.StoredRebindBoundaryChecks.actual_rows
