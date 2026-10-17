import MicroCFTA.SourceCurrentConstrainedCapCheckedJointCompile

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.CheckedJointCompileIntegration
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedEdgeResidency InternedNestedFacts InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceCurrentConstrainedCap (Cap)
open SourceCurrentConstrainedCapPairOccurrences (Classified sourceWeight)
open SourceCurrentConstrainedCapNonplainRank (pairRank)
open SourceCurrentConstrainedCapKernelJoint (Context)
open SourceCurrentConstrainedCapCheckedJointCode
variable {Symbol Guard : Type} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A literal bad-guard self branch retains cap one without a hereditary input assumption. -/
theorem constrained_self (annotation : Guard → Prop) (source : InternedConstructorTemplates.State Symbol Guard)
    (facts : Facts source) (state : Machine Symbol Guard) (context : Context annotation source state)
    (entry : Interned NodeKey) (edge : EdgeValue Symbol Guard) (level : Nat)
    (children : edge.children = []) (outside : ¬ annotation edge.entry.key.constraint)
    (available : Available source (.node entry [edge] level [])) :
    let input := Value.node entry [edge] level []
    compileNode ⟨IntersectionEmptyDomain.emptyDomain, input, input⟩ = .pure input ∧
      Cap annotation 1 input ∧
      Classified (sourceWeight annotation source) (pairRank annotation input input) input ∧
      ¬ SourceEqualityAnnotationLanguage.Annotated annotation input := by
  let input := Value.node entry [edge] level []
  have cap : Cap annotation 1 input := by
    apply Cap.node 0
    intro child member
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, children, List.not_mem_nil] at member
  have branch : SourceRecursiveIntersectionControl.decision IntersectionEmptyDomain.emptyDomain.key input input = .self := by
    simp [input, SourceRecursiveIntersectionControl.decision, SourceRecursiveIntersectionControl.hasEmpty,
      SourceRecursiveIntersectionControl.reset, SourceRecursiveIntersectionControl.closedSelf, Value.referenceOf, Value.free,
      IntersectionEmptyDomain.emptyDomain, IntersectionEmptyDomain.emptyKey]
  have compiled : compileNode ⟨IntersectionEmptyDomain.emptyDomain, input, input⟩ = .pure input := by
    simp only [compileNode, branch]
  have inputs := SourceCurrentConstrainedCapOriginalSupport.closed_inputs source facts IntersectionEmptyDomain.emptyDomain
    input input available available rfl rfl
  have cert := SourceCurrentConstrainedCapCheckedJointCompile.node_certified annotation source facts
    ⟨IntersectionEmptyDomain.emptyDomain, input, input⟩ 1 state context (empty_domain _)
    (SourceCurrentConstrainedCapOriginalSupport.empty annotation source) inputs cap cap
  rw [compiled] at cert
  refine ⟨compiled, cert.2.1, cert.2.2.1, ?_⟩
  intro plain
  exact outside (SourceCurrentHereditaryConstructors.node_edge plain edge List.mem_cons_self).1

/-- An actual Mu entry consumes a child law derived from literal Empty code and then finishes the unused binder. -/
theorem mixed_mu_empty_body (annotation : Guard → Prop) (source : InternedConstructorTemplates.State Symbol Guard)
    (facts : Facts source) (state : Machine Symbol Guard) (context : Context annotation source state)
    (nodeEntry muEntry : Interned NodeKey) (edge : EdgeValue Symbol Guard) (level : Nat)
    (children : edge.children = []) (outside : ¬ annotation edge.entry.key.constraint)
    (different : nodeEntry.identity ≠ muEntry.identity)
    (leftAvailable : Available source (.node nodeEntry [edge] level []))
    (rightAvailable : Available source (.mu muEntry .empty .empty .empty)) :
    let domain := IntersectionEmptyDomain.emptyDomain
    let left := Value.node nodeEntry [edge] level []
    let right := Value.mu muEntry .empty .empty .empty
    let actual := SourceRecursiveIntersectionEnvironment.enter state.domains domain.key left right nodeEntry.identity muEntry.identity
    let entered : Machine Symbol Guard := {state with domains := actual.2}
    compileNode ⟨domain, left, right⟩ = compileMu domain left right ∧
      Extension state entered ∧ Context annotation source entered ∧
      SourceCurrentConstrainedCapCheckedJointCompile.Post annotation source 1 ⟨domain, left, right⟩ entered .empty ∧
      ¬ SourceEqualityAnnotationLanguage.Annotated annotation left := by
  let domain := IntersectionEmptyDomain.emptyDomain
  let left := Value.node nodeEntry [edge] level []
  let right := Value.mu muEntry .empty .empty .empty
  let actual := SourceRecursiveIntersectionEnvironment.enter state.domains domain.key left right nodeEntry.identity muEntry.identity
  let entered : Machine Symbol Guard := {state with domains := actual.2}
  have cap : Cap annotation 1 left := by
    apply Cap.node 0
    intro child member
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, children, List.not_mem_nil] at member
  have rightCap : Cap annotation 1 right := .plain 1 (.mu muEntry .empty .empty .empty .empty)
  have inputs := SourceCurrentConstrainedCapOriginalSupport.closed_inputs source facts domain left right leftAvailable rightAvailable rfl rfl
  have branch : SourceRecursiveIntersectionControl.decision domain.key left right = .rightMu := by
    simp [domain, left, right, SourceRecursiveIntersectionControl.decision, SourceRecursiveIntersectionControl.hasEmpty,
      SourceRecursiveIntersectionControl.reset, SourceRecursiveIntersectionControl.closedSelf, SourceRecursiveIntersectionControl.greater,
      SourceRecursiveIntersectionControl.compareValue, SourceRecursiveIntersectionControl.tag,
      SourceRecursiveIntersectionControl.identity, SourceRecursiveIntersectionControl.payload,
      Value.referenceOf, Value.free, IntersectionEmptyDomain.emptyDomain, IntersectionEmptyDomain.emptyKey, different]
  have compiled : compileNode ⟨domain, left, right⟩ = compileMu domain left right := by simp only [compileNode, branch]
  have grownLeft := leftAvailable.grows source state.heap context.growth context.history
  have grownRight := rightAvailable.grows source state.heap context.growth context.history
  obtain ⟨validEntered, extension, knownEntered⟩ := SourceRecursiveIntersectionKernel.entered state context.valid domain (empty_domain _)
    left right grownLeft grownRight nodeEntry.identity muEntry.identity
  have enteredContext : Context annotation source entered :=
    ⟨validEntered, context.semantic, context.guards, context.growth, context.history⟩
  let child : NodeRequest Symbol Guard := ⟨actual.1, left, .empty⟩
  have childCode : compileNode child = .pure .empty := by
    simp [compileNode, child, SourceRecursiveIntersectionControl.decision, SourceRecursiveIntersectionControl.hasEmpty,
      Value.referenceOf]
  have childLaw := SourceCurrentConstrainedCapCheckedJointCompile.node_law_certified annotation source facts child entered enteredContext knownEntered
  rw [childCode] at childLaw
  have cert := SourceCurrentConstrainedCapCheckedJointCompile.node_certified annotation source facts
    ⟨domain, left, right⟩ 1 state context (empty_domain _) (SourceCurrentConstrainedCapOriginalSupport.empty annotation source) inputs cap rightCap
  rw [compiled] at cert
  simp only [compileMu, left, right, SourceRecursiveIntersectionControl.identity, Certified] at cert
  have result := cert extension enteredContext .empty entered (.refl _) enteredContext (empty_available _) childLaw
  have optionalDone : construction (SourceRecursiveIntersectionMaybeMu.maybeMu
      (SourceRecursiveIntersectionControl.pair nodeEntry.identity muEntry.identity) .empty entered.heap) entered = .done .empty entered := by
    simp [SourceRecursiveIntersectionMaybeMu.maybeMu, Value.free, construction]
  have final := result .empty entered optionalDone (.refl _) enteredContext
  refine ⟨compiled, extension, enteredContext, final, ?_⟩
  intro plain
  exact outside (SourceCurrentHereditaryConstructors.node_edge plain edge List.mem_cons_self).1

#print axioms constrained_self
#check @constrained_self
#print axioms mixed_mu_empty_body
#check @mixed_mu_empty_body
end MicroCFTA.CheckedJointCompileIntegration
