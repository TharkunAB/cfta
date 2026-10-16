import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryNode

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.funBinderTypes true

#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryNode.rows_certified
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryNode.rows_certified
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryNode.node_certified
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryNode.node_certified

namespace FiniteOrdinaryNodeChecks
open MicroCFTA Cache InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceCurrentAllocatedFiniteOrdinaryCode SourceCurrentAllocatedFiniteOrdinaryStored
open SourceEqualityRequiredSemanticCache (SemanticReady)
open MergedOrdinaryHeight (height)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Nonempty equality classes and arbitrary guards occur in both joined input rows. -/
theorem full_guards
    (symbol : Symbol) (firstGuard secondGuard : SourceGuards.Guard FullSyntax.Formula)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (semantic : SemanticReady state.heap) :
    let left : EdgeValue Symbol Guard := .mk ⟨0, ⟨symbol, [.empty, .empty],
      ⟨some [[[0], [1]]], firstGuard⟩⟩⟩ [.empty, .empty]
    let right : EdgeValue Symbol Guard := .mk ⟨1, ⟨symbol, [.empty, .empty],
      ⟨some [[[0], [1]]], secondGuard⟩⟩⟩ [.empty, .empty]
    Certified (compileRows IntersectionEmptyDomain.emptyDomain [left] [right]) state
      (fun _ value => NodeCertificate
        ⟨IntersectionEmptyDomain.emptyDomain, .node ⟨2, .node [0]⟩ [left] 0 [],
          .node ⟨3, .node [1]⟩ [right] 0 []⟩ value) := by
  apply SourceCurrentAllocatedFiniteOrdinaryNode.rows_certified
  · rfl
  · exact .cons (.cons .empty (.cons .empty .nil)) .nil
  · exact .cons (.cons .empty (.cons .empty .nil)) .nil
  · exact valid
  · exact semantic

/-- Physical self reuse returns a record bounded by both original operands. -/
theorem selected_self
    (request : NodeRequest Symbol Guard) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (semantic : SemanticReady state.heap)
    (leftAvailable : Available state.heap request.left) (rightAvailable : Available state.heap request.right)
    (inputs : NodeInputs request)
    (selected : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .self) :
    SourceCurrentAllocatedFiniteOrdinaryDomain.Node request.left ∧
      height request.left ≤ height request.left ∧ height request.left ≤ height request.right := by
  have certificate := SourceCurrentAllocatedFiniteOrdinaryNode.node_certified request state valid semantic
    leftAvailable rightAvailable inputs
  simp only [compileNode, selected, Certified] at certificate
  exact certificate inputs.1 inputs.2.1 inputs.2.2

/-- A reset uses the empty-seen child request and retains the original height bounds. -/
theorem selected_reset
    (request : NodeRequest Symbol Guard) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (semantic : SemanticReady state.heap)
    (leftAvailable : Available state.heap request.left) (rightAvailable : Available state.heap request.right)
    (inputs : NodeInputs request)
    (selected : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .reset) :
    Certified (requestNode IntersectionEmptyDomain.emptyDomain request.left request.right) state
      (fun _ value => NodeCertificate request value) := by
  simpa only [compileNode, selected] using
    SourceCurrentAllocatedFiniteOrdinaryNode.node_certified request state valid semantic leftAvailable rightAvailable inputs

/-- Reversed requests keep the result bound in each original operand's position. -/
theorem selected_swap
    (request : NodeRequest Symbol Guard) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (semantic : SemanticReady state.heap)
    (leftAvailable : Available state.heap request.left) (rightAvailable : Available state.heap request.right)
    (inputs : NodeInputs request)
    (selected : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .swap) :
    Certified (requestNode request.domain request.right request.left) state
      (fun _ value => NodeCertificate request value) := by
  simpa only [compileNode, selected] using
    SourceCurrentAllocatedFiniteOrdinaryNode.node_certified request state valid semantic leftAvailable rightAvailable inputs

end FiniteOrdinaryNodeChecks

#print axioms FiniteOrdinaryNodeChecks.full_guards
#check @FiniteOrdinaryNodeChecks.full_guards
#print axioms FiniteOrdinaryNodeChecks.selected_self
#check @FiniteOrdinaryNodeChecks.selected_self
#print axioms FiniteOrdinaryNodeChecks.selected_reset
#check @FiniteOrdinaryNodeChecks.selected_reset
#print axioms FiniteOrdinaryNodeChecks.selected_swap
#check @FiniteOrdinaryNodeChecks.selected_swap
