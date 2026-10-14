import MicroCFTA.SourceRecursiveIntersectionCompileChildBounds

/-!
# Strict limits through actual original binder lookup

Original source bindings retain their exact Mu payload after source growth.
Actual reference code therefore requests the same original binder as the
semantic schedule. Both operand orders retain the strict parent-body limit.
-/
namespace MicroCFTA.SourceRecursiveIntersectionCode
open Cache Binding BinderLanguage InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceRecursiveIntersectionInputView SourceRecursiveIntersectionNative IntersectSchedule
open SourceRecursiveIntersectionControl SourceRecursiveIntersectionSchedule

/-- Actual left-reference code derives original binder scope and the strict request limit after growth. -/
theorem leftReference_below [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (source : InternedConstructorTemplates.State Symbol Guard)
    (facts : Facts source) (holds : Guard → Language.Term Symbol → Bool) (domain : Interned DomainKey) (name : Nat) (right : Value Symbol Guard)
    (scope : NodeScope source ⟨domain, .reference (.interned name), right⟩)
    (complete : Completes (view source holds) (nodeSemantic ⟨domain, .reference (.interned name), right⟩))
    (selected : decision domain.key (.reference (.interned name)) right = .leftReference)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (growth : Grows source state.heap) (history : Extends source.nodes.issued state.heap.nodes.issued) :
    Below source holds (requiredFuel (view source holds) (nodeSemantic ⟨domain, .reference (.interned name), right⟩) complete)
      (compileReference domain name right true) state := by
  by_cases bound : name ∈ SourceRecursiveIntersectionDomain.names domain.key
  · obtain ⟨value, found, original, available, encoded⟩ := scope.bindings.read source state.heap valid.1 growth history domain.key name bound
    have childScope : NodeScope source ⟨domain, value, right⟩ := ⟨original, scope.right, available, scope.rightAvailable, scope.bindings⟩
    have childBound : NodeBelow source holds
        (requiredFuel (view source holds) (nodeSemantic ⟨domain, .reference (.interned name), right⟩) complete) ⟨domain, value, right⟩ := by
      apply node_child_below source facts holds _ _ scope complete childScope
      simp only [selected, branchCalls, nodeSemantic, inputOf, Value.referenceOf, IntersectionFlatMemoKey.input, Option.getD_some,
        lookup_domain, bound, ite_true, Option.toList_some, List.map_cons, List.map_nil, List.mem_singleton]
      exact congrArg (fun input => Call.node (SourceRecursiveIntersectionSchedule.domain domain.key) input (inputOf right)) encoded
    simp only [compileReference, bound, ite_true, Below, found]
    exact below_requestNode source holds _ _ state childBound
  · obtain ⟨fuel, result, action⟩ := successful_action source facts holds ⟨domain, .reference (.interned name), right⟩ scope complete
    simp only [selected, inputOf, Value.referenceOf, IntersectionFlatMemoKey.input, Option.getD_some,
      SourceRecursiveIntersectionStep.action, lookup_domain, bound, ite_false] at action
    cases action

/-- Actual right-reference code derives original binder scope and the strict request limit after growth. -/
theorem rightReference_below [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (source : InternedConstructorTemplates.State Symbol Guard)
    (facts : Facts source) (holds : Guard → Language.Term Symbol → Bool) (domain : Interned DomainKey) (left : Value Symbol Guard) (name : Nat)
    (scope : NodeScope source ⟨domain, left, .reference (.interned name)⟩)
    (complete : Completes (view source holds) (nodeSemantic ⟨domain, left, .reference (.interned name)⟩))
    (selected : decision domain.key left (.reference (.interned name)) = .rightReference)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (growth : Grows source state.heap) (history : Extends source.nodes.issued state.heap.nodes.issued) :
    Below source holds (requiredFuel (view source holds) (nodeSemantic ⟨domain, left, .reference (.interned name)⟩) complete)
      (compileReference domain name left false) state := by
  by_cases bound : name ∈ SourceRecursiveIntersectionDomain.names domain.key
  · obtain ⟨value, found, original, available, encoded⟩ := scope.bindings.read source state.heap valid.1 growth history domain.key name bound
    have childScope : NodeScope source ⟨domain, left, value⟩ := ⟨scope.left, original, scope.leftAvailable, available, scope.bindings⟩
    have childBound : NodeBelow source holds
        (requiredFuel (view source holds) (nodeSemantic ⟨domain, left, .reference (.interned name)⟩) complete) ⟨domain, left, value⟩ := by
      apply node_child_below source facts holds _ _ scope complete childScope
      simp only [selected, branchCalls, nodeSemantic, inputOf, Value.referenceOf, IntersectionFlatMemoKey.input, Option.getD_some,
        lookup_domain, bound, ite_true, Option.toList_some, List.map_cons, List.map_nil, List.mem_singleton]
      exact congrArg (fun input => Call.node (SourceRecursiveIntersectionSchedule.domain domain.key) (inputOf left) input) encoded
    simp only [compileReference, bound, ite_true, Below, found]
    exact below_requestNode source holds _ _ state childBound
  · obtain ⟨fuel, result, action⟩ := successful_action source facts holds ⟨domain, left, .reference (.interned name)⟩ scope complete
    simp only [selected, inputOf, Value.referenceOf, IntersectionFlatMemoKey.input, Option.getD_some,
      SourceRecursiveIntersectionStep.action, lookup_domain, bound, ite_false] at action
    cases action

end MicroCFTA.SourceRecursiveIntersectionCode
