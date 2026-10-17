import MicroCFTA.SourceCurrentConstrainedCapKernelJointDecision

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option pp.fullNames true
set_option maxRecDepth 30000

namespace MicroCFTA.JointDecisionKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedConstruction (Syntax Outcome)
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionControl
open SourceCurrentConstrainedCapNativeOccurrenceCache (NodeInputs OriginalBindings)

private def plan : Syntax Nat Bool := .node [.mk 2 true [.node [.mk 0 false []], .node [.mk 1 false []]]]
private def first : Value Nat Bool := .node {identity := 0, key := .node [0]}
  [.mk {identity := 0, key := ⟨0, [], false⟩} []] 0 []
private def second : Value Nat Bool := .node {identity := 1, key := .node [1]}
  [.mk {identity := 1, key := ⟨1, [], false⟩} []] 0 []
private def root : Value Nat Bool := .node {identity := 2, key := .node [2]}
  [.mk {identity := 2, key := ⟨2, [.node 0, .node 1], true⟩} [first, second]] 0 []
private def resetDomain : Interned DomainKey := ⟨0, ⟨[(99, .mu 99)], []⟩⟩
private def repeatedDomain : Interned DomainKey := ⟨0, ⟨[], [(0, 1)]⟩⟩

set_option cbv.maxSteps 100000000 in
private theorem computed :
    (match InternedFreshOrdinaryConstruction.build plan [] empty with
    | .done value _ => value = root | .pending .. => False) := by cbv

/-- One actual closed source supplies both reset coverage and the exact repeated-pair source weight. -/
theorem constructed_decisions :
    ∃ source, InternedFreshOrdinaryConstruction.build plan [] empty = .done root source ∧
      decision resetDomain.key first first = .reset ∧
      NodeInputs source ⟨IntersectionEmptyDomain.emptyDomain, first, first⟩ ∧
      decision repeatedDomain.key first second = .repeated (0, 1) ∧
      SourceCurrentConstrainedCapPairOccurrences.sourceWeight (fun guard : Bool => guard = true) source (.intersection 0 1) =
        SourceCurrentConstrainedCapNonplainRank.pairRank (fun guard : Bool => guard = true) first second := by
  obtain ⟨value, source, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete plan
  have same : value = root := by simpa only [done] using computed
  subst value
  have physical := InternedFreshOrdinaryFacts.closed_verified plan
  have resident := physical.result root source done
  have facts : Facts source := by simpa only [done, Outcome.state] using physical.facts
  have leftAvailable : Available source first := resident.children first (by simp [root, InternedProbeProvenance.children])
  have rightAvailable : Available source second := resident.children second (by simp [root, InternedProbeProvenance.children])
  have resetInputs := SourceCurrentConstrainedCapOriginalSupport.closed_inputs source facts resetDomain first first
    leftAvailable leftAvailable rfl rfl
  have resetSelected : decision resetDomain.key first first = .reset := by cbv
  have emptyInputs := SourceCurrentConstrainedCapKernelJointDecision.reset_inputs source resetDomain first first resetInputs resetSelected
  have pairInputs := SourceCurrentConstrainedCapOriginalSupport.closed_inputs source facts repeatedDomain first second
    leftAvailable rightAvailable rfl rfl
  have originalBindings : OriginalBindings (fun guard : Bool => guard = true) source repeatedDomain.key := by
    intro name absent
    cases absent
  have repeatedSelected : decision repeatedDomain.key first second = .repeated (0, 1) := by cbv
  have exactWeight := SourceCurrentConstrainedCapKernelJointDecision.repeated_weight
    (fun guard : Bool => guard = true) source facts repeatedDomain first second originalBindings pairInputs (0, 1) repeatedSelected
  exact ⟨source, done, resetSelected, emptyInputs, repeatedSelected, exactWeight⟩

#print axioms constructed_decisions
#check @constructed_decisions
end MicroCFTA.JointDecisionKernels
