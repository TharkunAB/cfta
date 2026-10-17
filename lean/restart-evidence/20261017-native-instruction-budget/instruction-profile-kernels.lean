import MicroCFTA.SourceRecursiveIntersectionInstructionProfile
import MicroCFTA.InternedFreshOrdinaryClosedCompletion
import MicroCFTA.InternedFreshOrdinaryFacts
import MicroCFTA.InternedFreshOrdinarySourceFreeNames
import MicroCFTA.SourceRecursiveIntersectionOriginalOutput

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option pp.fullNames true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.InstructionProfileKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedEdgeResidency
open InternedNestedConstruction (Syntax Outcome)
open SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceRecursiveIntersectionInputView (Original)
open SourceRecursiveIntersectionInstructionProfile

/-- Arbitrary closed source syntax produces its own initial scope and branching credit. -/
theorem closed_source_credit {Symbol Guard : Type} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (height : Nat) (positive : 0 < height) :
    ∃ value source,
      InternedFreshOrdinaryConstruction.build expression [] empty = .done value source ∧
      Facts source ∧ NodeScope source ⟨IntersectionEmptyDomain.emptyDomain, value, value⟩ ∧
      (SourceRecursiveIntersectionKernel.pairs (nodeEdges value) (nodeEdges value)).length ≤ sourceBranching source ∧
      SourceRecursiveIntersectionSourceProfile.memberCount value ≤ sourceBranching source ∧
      1 ≤ sourceBranching source ∧
      4 ≤ budget (sourceBranching source) height ∧
      budget (sourceBranching source) height ≤ budget (sourceBranching source) (height + 1) := by
  obtain ⟨value, source, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  have verified := InternedFreshOrdinaryFacts.closed_verified expression
  have facts : Facts source := by simpa only [done, Outcome.state] using verified.facts
  have available := verified.result value source done
  have closed := InternedFreshOrdinarySourceFreeNames.closed_free_empty expression value source done
  have original := SourceRecursiveIntersectionOriginalOutput.closed_original value source facts.coherent available closed
  have scope := initial_scope source value value original original available available
  exact ⟨value, source, done, facts, scope, row_pairs source facts _ scope,
    left_members source facts _ scope, sourceBranching_pos source,
    budget_ge_four _ height positive, budget_succ_ge _ height⟩

private def plan : Syntax Nat Bool := .union [
  .binder false (.node [.mk 0 true [.var 0]]),
  .node [.mk 1 false [], .mk 2 true [.node [.mk 3 true []], .node [.mk 3 true []]]]]
private def built := InternedFreshOrdinaryConstruction.build plan [] empty
private def source := built.state
private def root : Value Nat Bool := match built with | .done value _ => value | .pending .. => .empty
private def ordinary : Value Nat Bool := (InternedProbeProvenance.children root)[1]?.getD .empty
private def selected : EdgeValue Nat Bool := (nodeEdges ordinary)[1]?.getD (.mk ⟨0, ⟨0, [], true⟩⟩ [])

private theorem constructed : built = .done root source := by
  obtain ⟨value, state, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete plan
  simp only [built, root, source, done, Outcome.state]

private theorem source_facts : Facts source :=
  (InternedFreshOrdinaryFacts.closed_verified plan).facts

private theorem root_available : Available source root :=
  (InternedFreshOrdinaryFacts.closed_verified plan).result root source constructed

private theorem root_original : Original root :=
  SourceRecursiveIntersectionOriginalOutput.closed_original root source source_facts.coherent root_available
    (InternedFreshOrdinarySourceFreeNames.closed_free_empty plan root source constructed)

private theorem ordinary_member : ordinary ∈ InternedProbeProvenance.children root := by
  have found : (InternedProbeProvenance.children root)[1]? = some ordinary := by cbv
  exact List.mem_of_getElem? found

private theorem ordinary_available : Available source ordinary := root_available.children ordinary ordinary_member

private theorem ordinary_original : Original ordinary :=
  SourceRecursiveIntersectionOriginalOutput.closed_original ordinary source source_facts.coherent ordinary_available (by cbv)

private theorem selected_member : selected ∈ nodeEdges ordinary := by
  have found : (nodeEdges ordinary)[1]? = some selected := by cbv
  exact List.mem_of_getElem? found

private theorem selected_scope : EdgeScope source ⟨IntersectionEmptyDomain.emptyDomain, selected, selected⟩ := by
  have scope := initial_scope source ordinary ordinary ordinary_original ordinary_original ordinary_available ordinary_available
  have present := selected_member
  cases originalShape : ordinary with
  | empty | reference | mu | union => simp [originalShape, nodeEdges] at present
  | node entry edges depth free =>
      have ready : NodeScope source ⟨IntersectionEmptyDomain.emptyDomain,
          .node entry edges depth free, .node entry edges depth free⟩ := by simpa only [originalShape] using scope
      have member : selected ∈ edges := by simpa only [originalShape, nodeEdges] using selected_member
      exact NodeScope.rows source source_facts _ entry edges depth free entry edges depth free ready selected selected member member

/-- One actual recursive union supplies nonzero member, row-pair, and child-zip bounds. -/
theorem recursive_source_branches :
    InternedFreshOrdinaryConstruction.build plan [] empty = .done root source ∧
    NodeScope source ⟨IntersectionEmptyDomain.emptyDomain, root, root⟩ ∧
    EdgeScope source ⟨IntersectionEmptyDomain.emptyDomain, selected, selected⟩ ∧
    SourceRecursiveIntersectionSourceProfile.memberCount root = 2 ∧
    (SourceRecursiveIntersectionKernel.pairs (nodeEdges ordinary) (nodeEdges ordinary)).length = 2 ∧
    (selected.children.zip selected.children).length = 2 ∧
    sourceBranching source = 36 ∧
    (SourceRecursiveIntersectionKernel.pairs (nodeEdges ordinary) (nodeEdges ordinary)).length ≤ sourceBranching source ∧
    (selected.children.zip selected.children).length ≤ sourceBranching source ∧
    SourceRecursiveIntersectionSourceProfile.memberCount root ≤ sourceBranching source ∧
    budget (sourceBranching source) 3 = 5332 := by
  have rootScope := initial_scope source root root root_original root_original root_available root_available
  have ordinaryScope := initial_scope source ordinary ordinary ordinary_original ordinary_original ordinary_available ordinary_available
  exact ⟨constructed, rootScope, selected_scope, by cbv, by cbv, by cbv, by cbv,
    row_pairs source source_facts _ ordinaryScope, edge_zip source source_facts _ selected_scope,
    right_members source source_facts _ rootScope, by cbv⟩

end MicroCFTA.InstructionProfileKernels

#print axioms MicroCFTA.InstructionProfileKernels.closed_source_credit
#check @MicroCFTA.InstructionProfileKernels.closed_source_credit
#print axioms MicroCFTA.InstructionProfileKernels.recursive_source_branches
#check @MicroCFTA.InstructionProfileKernels.recursive_source_branches
