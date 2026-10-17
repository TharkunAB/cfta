import MicroCFTA.SourceCurrentConstrainedCapKernelJointRows
import MicroCFTA.SourceCurrentConstrainedCapGuardExecution

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option format.width 200
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000

namespace MicroCFTA.JointRowsKernel
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency InternedNestedFacts
open InternedNestedConstruction (Syntax Outcome)
open SourceRecursiveIntersectionKernel
open SourceCurrentConstrainedCapKernelJoint (Context)
local notation "Heap" => InternedConstructorTemplates.State Nat Bool
local notation "V" => Value Nat Bool
private def annotation (guard : Bool) : Prop := guard = true
private def expression : Syntax Nat Bool := .union [.node [.mk 7 false []], .node [.mk 7 true []]]
private def built := InternedFreshOrdinaryConstruction.build expression [] (empty : Heap)
private def heap := built.state
private def root : V := match built with | .done value _ => value | .pending .. => .empty
private def left : V := .node ⟨0, .node [0]⟩ [.mk ⟨0, ⟨7, [], false⟩⟩ []] 0 []
private def right : V := .node ⟨1, .node [1]⟩ [.mk ⟨1, ⟨7, [], true⟩⟩ []] 0 []
private def state : Machine Nat Bool := ⟨heap, Cache.emptyState⟩
private def domain := IntersectionEmptyDomain.emptyDomain
private def call := SourceRecursiveIntersectionKernel.execute (Symbol := Nat) true Bool.and 0
private theorem source_done : built = .done root heap := by cbv
private theorem left_present : heap.nodeRecords (.node [0]) = some left := by cbv
private theorem right_present : heap.nodeRecords (.node [1]) = some right := by cbv
private theorem node_done : node true Bool.and (call domain) (nodeEdges left) (nodeEdges right) state = .done left state := by cbv

/-- A nonempty matched source row walk derives its own constrained result and full joint context; all constructor hits retain the exact heap. -/
theorem constructed_nullary_rows :
    InternedFreshOrdinaryConstruction.build expression [] (empty : Heap) = .done root heap ∧
      node true Bool.and (call domain) (nodeEdges left) (nodeEdges right) state = .done left state ∧
      Context annotation heap state ∧ Available state.heap left ∧ SourceCurrentConstrainedCap.Cap annotation 1 left ∧
      SourceCurrentConstrainedCapPairOccurrences.Classified
        (SourceCurrentConstrainedCapPairOccurrences.sourceWeight annotation heap)
        (SourceCurrentConstrainedCapNonplainRank.pairRank annotation left right) left ∧
      SourceRecursiveIntersectionResultScope.Scope domain.key.seen left := by
  have semantic := SourceRecursiveIntersectionSemanticHeap.constructed expression root heap source_done
  have facts := semantic.1.normal.facts
  have guards : SourceCurrentConstrainedCapGuardHeap.Heap annotation heap := by
    exact SourceCurrentConstrainedCapGuardExecution.closed_heap annotation expression
  have context : Context annotation heap state := ⟨⟨facts, Cache.empty_valid⟩, semantic, guards, grows_refl _, extends_refl _⟩
  have leftAvailable := facts.cached.nodes _ _ left_present
  have rightAvailable := facts.cached.nodes _ _ right_present
  have inputs := SourceCurrentConstrainedCapOriginalSupport.closed_inputs heap facts domain left right leftAvailable rightAvailable rfl rfl
  have leftCap : SourceCurrentConstrainedCap.Cap annotation 1 left := by
    apply SourceCurrentConstrainedCap.Cap.node 0
    intro child impossible
    cases impossible
  have rightCap : SourceCurrentConstrainedCap.Cap annotation 1 right := by
    apply SourceCurrentConstrainedCap.Cap.node 0
    intro child impossible
    cases impossible
  have physical := execute_checked true Bool.and 0
  have joint : SourceCurrentConstrainedCapKernelJoint.Calls annotation heap call := by
    intro depth known first second current _ _ _ _ _ _
    exact SourceCurrentConstrainedCapKernelJoint.failed annotation heap current .exhausted _
  have observed := SourceCurrentConstrainedCapKernelJointRows.node_joint annotation heap true Bool.and call physical joint
    rfl (by intro first second firstGood secondGood; cases firstGood; cases secondGood; rfl)
    1 domain left right facts state context (empty_domain _) (SourceCurrentConstrainedCapOriginalSupport.empty annotation heap)
    inputs leftCap rightCap
  have returned := observed left state node_done
  exact ⟨source_done, node_done, returned.1, returned.2⟩

#print axioms constructed_nullary_rows
#check @constructed_nullary_rows
end MicroCFTA.JointRowsKernel
