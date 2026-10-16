import MicroCFTA.SourceCurrentAllocatedRecursivePrefixCode
set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option format.width 200

namespace MicroCFTA.RecursivePrefixCode2Kernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityRequiredSemanticCache (SemanticReady)
open IntersectionFlatMemoKeyDomain
open SourceCurrentAllocatedRecursivePrefixCode
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- A source Mu dispatcher constructs a ready body request in its actual new domain. -/
theorem entered_body [DecidableEq Symbol]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (request : NodeRequest Symbol Guard) (scope : NodeScope source request)
    (member : request.domain.key ∈ SourceRecursiveIntersectionSourceInventory.domains source)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (semantic : SemanticReady state.heap) (ready : NodeReady state request)
    (growth : Grows source state.heap) (history : Extends source.nodes.issued state.heap.nodes.issued)
    (first second : Nat)
    (leftId : SourceRecursiveIntersectionControl.identity request.left = some first)
    (rightId : SourceRecursiveIntersectionControl.identity request.right = some second)
    (branch : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .bothMu) :
    let entered := SourceRecursiveIntersectionEnvironment.enter state.domains request.domain.key
      request.left request.right first second
    let after : Machine Symbol Guard := {state with domains := entered.2}
    SourceRecursiveIntersectionKernel.Valid after ∧ Extension state after ∧ SemanticReady after.heap ∧
      NodeReady after ⟨entered.1, body request.left, body request.right⟩ ∧
      NodeScope source ⟨entered.1, body request.left, body request.right⟩ ∧
      entered.1.key ∈ SourceRecursiveIntersectionSourceInventory.domains source := by
  have certificate := node_certified source (SourceRecursiveIntersectionSourceInventory.domains source) facts
    (SourceCurrentAllocatedRecursiveDomainCode.source_closed source facts) request scope member
    state valid semantic ready growth history
  have enteredCertificate : Certified source (SourceRecursiveIntersectionSourceInventory.domains source)
      (.enter request.domain request.left request.right first second
        (fun entered => .node ⟨entered, body request.left, body request.right⟩
          (fun value => .optionalBinder (SourceRecursiveIntersectionControl.pair first second) value .pure)))
      state (fun after value => Available after.heap value) := by
    simpa only [compileNode, branch, compileMu, leftId, rightId] using certificate
  have actual := enter_next source _ request.domain request.left request.right first second _ state _ enteredCertificate semantic
  have current := node_data source _ _ _ _ _ actual.2.2.2
  exact ⟨actual.1, actual.2.1, actual.2.2.1, current⟩

/-- Available constructor inputs produce a resident edge and the exact next certificate. -/
theorem actual_edge_work
    (source : InternedConstructorTemplates.State Symbol Guard) (inventory : List DomainKey)
    (symbol : Symbol) (guard : Guard) (values : List (Value Symbol Guard)) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (semantic : SemanticReady state.heap)
    (available : ∀ value ∈ values, Available state.heap value) :
    let actual := run (makeEdge symbol guard values) state.heap
    let after : Machine Symbol Guard := {state with heap := actual.2}
    SourceRecursiveIntersectionKernel.Valid after ∧ Extension state after ∧ SemanticReady after.heap ∧
      EdgeResident after.heap actual.1 ∧ after.domains = state.domains := by
  let job := makeEdge symbol guard values
  have safe := safe_work job state valid EdgeResident
    (InternedNestedFacts.edge_verified symbol guard values state.heap valid.1 available)
  have certificate : Certified source inventory (.work job .pure) state (fun after edge => EdgeResident after.heap edge) := by
    refine ⟨safe, ⟨.edge symbol guard values available, ?_⟩, ?_⟩
    · intro _ _ _; trivial
    · intro value after done _ _ _
      exact safe.2.2 value after done
  have actual := work_next source inventory job .pure state _ certificate semantic _ _ rfl
  exact ⟨actual.1, actual.2.1, actual.2.2.1, pure_result source inventory _ _ _ actual.2.2.2, rfl⟩

/-- A literal optional-binder return derives its own post and semantic heap. -/
theorem actual_optional_binder
    (source : InternedConstructorTemplates.State Symbol Guard) (inventory : List DomainKey)
    (pair : Nat × Nat) (body : Value Symbol Guard) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (semantic : SemanticReady state.heap)
    (available : Available state.heap body) (value : Value Symbol Guard) (after : Machine Symbol Guard)
    (done : construction (SourceRecursiveIntersectionMaybeMu.maybeMu pair body state.heap) state = .done value after) :
    SourceRecursiveIntersectionKernel.Valid after ∧ Extension state after ∧ SemanticReady after.heap ∧
      Available after.heap value := by
  have safe := safe_optionalBinder pair body state valid available
  have certificate : Certified source inventory (.optionalBinder pair body .pure) state
      (fun after value => Available after.heap value) := by
    refine ⟨safe, ⟨available, ?_⟩, ?_⟩
    · intro _ _ _; trivial
    · intro result final completed _ _ _
      exact safe.2.2 result final completed
  have actual := optionalBinder_next source inventory pair body .pure state _ certificate semantic value after done
  exact ⟨actual.1, actual.2.1, actual.2.2.1, pure_result source inventory value after _ actual.2.2.2⟩

#print axioms entered_body
#check @entered_body
#print axioms actual_edge_work
#check @actual_edge_work
#print axioms actual_optional_binder
#check @actual_optional_binder
end MicroCFTA.RecursivePrefixCode2Kernels
