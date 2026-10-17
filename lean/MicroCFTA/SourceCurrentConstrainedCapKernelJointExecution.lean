import MicroCFTA.SourceCurrentConstrainedCapKernelJointCalls
import MicroCFTA.SourceCurrentConstrainedCapKernelJointRows
import MicroCFTA.SourceCurrentConstrainedCapKernelJointDecision

/-!
# Joint finite-cap and occurrence laws for actual recursive execution

The induction follows the actual source recursion bound. Every smaller call
produces its own result laws and joint context. Mu calls can keep the same
positive rank. Original source reads and actual selected winners determine
their laws. This theorem does not assume completed recursive receipts.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapKernelJoint
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance InternedNestedFacts InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel
open SourceRecursiveIntersectionControl (decision repeatedValue)
open SourceCurrentConstrainedCap (Cap)
open SourceCurrentConstrainedCapNativeOccurrenceCache (OriginalBindings NodeInputs)
open SourceCurrentConstrainedCapPairOccurrences (Classified sourceWeight)
open SourceCurrentConstrainedCapNonplainRank (rank pairRank)
open SourceRecursiveIntersectionResultScope (Scope)
variable {Symbol Guard : Type} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Every actual source branch derives the joint local result from its smaller actual calls. -/
theorem onNode_joint (annotation : Guard → Prop) (source : State Symbol Guard) (facts : Facts source)
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (emptyValid : annotation emptyGuard)
    (conjoinValid : ∀ first second, annotation first → annotation second → annotation (conjoin first second))
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (physical : SourceRecursiveIntersectionKernel.Calls call) (joint : Calls annotation source call)
    (depth : Nat) (domain : Interned DomainKey) (left right : Value Symbol Guard) (state : Machine Symbol Guard)
    (context : Context annotation source state) (known : Domain state domain)
    (bindings : OriginalBindings annotation source domain.key) (inputs : NodeInputs source ⟨domain, left, right⟩)
    (leftCap : Cap annotation depth left) (rightCap : Cap annotation depth right) :
    Checked annotation source (onNode emptyGuard conjoin call domain left right state)
      (fun after value => Available after.heap value ∧ Cap annotation depth value ∧
        Classified (sourceWeight annotation source) (pairRank annotation left right) value ∧ Scope domain.key.seen value) := by
  cases selected : decision domain.key left right with
  | empty =>
      simp only [onNode, selected]
      exact pure annotation source state context (Value.empty : Value Symbol Guard) _ ⟨empty_available state.heap, .plain depth .empty,
        SourceCurrentConstrainedCapPairOccurrences.empty _ _, SourceRecursiveIntersectionResultScope.closed _ _ rfl⟩
  | reset =>
      simp only [onNode, selected]
      have resetInputs := SourceCurrentConstrainedCapKernelJointDecision.reset_inputs source domain left right inputs selected
      apply map annotation source _ _ _
        (joint depth IntersectionEmptyDomain.emptyDomain left right state context (empty_domain state)
          (SourceCurrentConstrainedCapOriginalSupport.empty annotation source) resetInputs leftCap rightCap)
      intro value after _ returned
      exact ⟨returned.1, returned.2.1, returned.2.2.1,
        SourceRecursiveIntersectionResultScope.weaken [] domain.key.seen (by intro pair member; cases member) value returned.2.2.2⟩
  | self =>
      simp only [onNode, selected]
      exact pure annotation source state context left _
        ⟨inputs.2.2.1.grows source state.heap context.growth context.history, leftCap,
          SourceCurrentConstrainedCapOriginalSupport.classified annotation source facts left inputs.1 inputs.2.2.1 _,
          SourceRecursiveIntersectionResultScope.closed _ _ (SourceRecursiveIntersectionResultScope.self_closed _ _ _ selected)⟩
  | swap =>
      simp only [onNode, selected]
      simpa only [pairRank, Nat.add_comm] using joint depth domain right left state context known bindings
        ⟨inputs.2.1, inputs.1, inputs.2.2.2.1, inputs.2.2.1, inputs.2.2.2.2.2, inputs.2.2.2.2.1⟩ rightCap leftCap
  | repeated key =>
      simp only [onNode, selected]
      have weight := SourceCurrentConstrainedCapKernelJointDecision.repeated_weight annotation source facts domain left right
        bindings inputs key selected
      exact pure annotation source state context (repeatedValue key) _
        ⟨reference_available state.heap _ (by intro name member; simp [Value.free] at member),
          .plain depth (.reference _), SourceCurrentConstrainedCapPairOccurrences.reference _ _ _ (by rw [weight]; exact Nat.le_refl _),
          SourceRecursiveIntersectionResultScope.repeated domain.key.seen key
            (SourceRecursiveIntersectionResultScope.repeated_seen _ _ _ key selected)⟩
  | bothMu | leftMu | rightMu =>
      simp only [onNode, selected]
      exact mu_joint annotation source facts call joint depth domain left right state context known bindings inputs leftCap rightCap
  | leftUnion =>
      simp only [onNode, selected]
      cases left with
      | empty | reference | node | mu => exact failed annotation source state _ _
      | union entry members level free =>
          exact SourceCurrentConstrainedCapKernelJointRows.left_union_joint annotation source call physical joint depth domain
            entry members level free right facts state context known bindings inputs leftCap rightCap
  | rightUnion =>
      simp only [onNode, selected]
      cases right with
      | empty | reference | node | mu => exact failed annotation source state _ _
      | union entry members level free =>
          exact SourceCurrentConstrainedCapKernelJointRows.right_union_joint annotation source call physical joint depth domain
            left entry members level free facts state context known bindings inputs leftCap rightCap
  | leftReference =>
      simp only [onNode, selected]
      cases left with
      | empty | node | union | mu => exact failed annotation source state _ _
      | reference name =>
          cases name <;> try exact failed annotation source state _ _
          rename_i name
          simpa only [pairRank, SourceCurrentConstrainedCapNonplainRank.reference_zero, Nat.zero_add] using
            reference_joint annotation source call joint depth domain name right true state context known bindings
              inputs.2.1 inputs.2.2.2.1 inputs.2.2.2.2.2 rightCap
  | rightReference =>
      simp only [onNode, selected]
      cases right with
      | empty | node | union | mu => exact failed annotation source state _ _
      | reference name =>
          cases name <;> try exact failed annotation source state _ _
          rename_i name
          simpa only [pairRank, SourceCurrentConstrainedCapNonplainRank.reference_zero, Nat.add_zero] using
            reference_joint annotation source call joint depth domain name left false state context known bindings
              inputs.1 inputs.2.2.1 inputs.2.2.2.2.1 leftCap
  | ordinary =>
      simp only [onNode, selected]
      cases left <;> cases right <;> try exact failed annotation source state _ _
      rename_i first firstRows firstDepth firstFree second secondRows secondDepth secondFree
      exact SourceCurrentConstrainedCapKernelJointRows.node_joint annotation source emptyGuard conjoin call physical joint
        emptyValid conjoinValid depth domain (.node first firstRows firstDepth firstFree) (.node second secondRows secondDepth secondFree)
        facts state context known bindings inputs leftCap rightCap
  | unsupported =>
      simp only [onNode, selected]
      exact failed annotation source state _ _

/-- Actual bounded recursive source execution produces its joint result laws without a future-call law premise. -/
theorem execute_joint (annotation : Guard → Prop) (source : State Symbol Guard) (facts : Facts source)
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (emptyValid : annotation emptyGuard)
    (conjoinValid : ∀ first second, annotation first → annotation second → annotation (conjoin first second)) (fuel : Nat) :
    Calls annotation source (execute (Symbol := Symbol) emptyGuard conjoin fuel) := by
  induction fuel with
  | zero =>
      intro depth domain left right state _context _known _bindings _inputs _leftCap _rightCap
      exact failed annotation source state .exhausted _
  | succ fuel ih =>
      intro depth domain left right state context known bindings inputs leftCap rightCap
      exact onNode_joint annotation source facts emptyGuard conjoin emptyValid conjoinValid _
        (execute_checked emptyGuard conjoin fuel) ih depth domain left right state context known bindings inputs leftCap rightCap

end MicroCFTA.SourceCurrentConstrainedCapKernelJoint
