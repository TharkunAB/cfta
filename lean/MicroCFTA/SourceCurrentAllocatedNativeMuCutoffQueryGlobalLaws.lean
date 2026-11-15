import MicroCFTA.SourceCurrentAllocatedNativeSourceQueryInduction
import MicroCFTA.SourceCurrentAllocatedNativeTopRowQueryGlobalLaws
import MicroCFTA.SourceCurrentAllocatedNativeRawMuCutoffReplay

/-!
# Exact selected Mu cutoffs with the existing complete query laws

One literal selected leftMu request retains its expected complete value.
The actual child compiler equation holds at each valid current domain cache.
The same executions retain the existing top-row and mismatch edge laws.
Both native memo tables start empty in the initial corollaries.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeMuCutoffQueryGlobalLaws
open Cache InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeContextCache (Returned)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
open SourceCurrentAllocatedNativeQueryGlobalLaws (MismatchResult)
open SourceCurrentAllocatedNativeTopRowQueryGlobalLaws (EdgeResult)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid
variable {width : Nat}

set_option autoImplicit false

/-- Existing exact node clauses also retain one literal selected Mu cutoff. -/
def NodeResult [DecidableEq Symbol] (target : NodeRequest Symbol Guard)
    (expected : Value Symbol Guard) (request : NodeRequest Symbol Guard)
    (value : Value Symbol Guard) : Prop :=
  SourceCurrentAllocatedNativePureQueryGlobalLaws.NodeResult request value ∧
    (request = target → value = expected)

private theorem cutoff_and_mismatch
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (target : NodeRequest Symbol Guard) (expected : Value Symbol Guard) (firstId secondId : Nat)
    (selected : SourceRecursiveIntersectionControl.decision target.domain.key target.left target.right = .leftMu)
    (leftIdentity : SourceRecursiveIntersectionControl.identity target.left = some firstId)
    (rightIdentity : SourceRecursiveIntersectionControl.identity target.right = some secondId)
    (childPure : ∀ current : Cache.State IntersectionFlatMemoKeyDomain.DomainKey, Cache.Valid current →
      compileNode ⟨(SourceRecursiveIntersectionEnvironment.enter current target.domain.key
        target.left target.right firstId secondId).1,
        SourceRecursiveIntersectionKernel.body target.left,
        SourceRecursiveIntersectionKernel.body target.right⟩ = .pure expected)
    (absent : let binder := SourceRecursiveIntersectionControl.pair firstId secondId
      InternedBinderProtocol.Reference.intersection binder.1 binder.2 ∉ expected.free)
    (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (fuel : Nat) :
    (∀ (request : NodeRequest Symbol Guard) (before : Checked width),
      Physical before.native → Grows sourceHeap before.native.machine.heap →
      SourceEqualityConstraintMemoAllocation.Valid before.operations →
      InputsThrough fuel (.code (.node request .pure)) before →
      SourceEqualityNativeDemandOperations.FieldsThrough fuel (.code (.node request .pure)) before →
      Returned (NodeResult target expected) before.native.nodes → Returned MismatchResult before.native.edges →
      (Returned (NodeResult target expected) (execute fuel (.code (.node request .pure)) before).state.native.nodes ∧
        Returned MismatchResult (execute fuel (.code (.node request .pure)) before).state.native.edges) ∧
      (∀ (count : Nat) (value : Value Symbol Guard) (after : Checked width), count ≤ fuel →
        Steps count (.code (.node request .pure)) before (.code (.pure value)) after →
        NodeResult target expected request value)) ∧
    (∀ (request : EdgeRequest Symbol Guard) (before : Checked width),
      Physical before.native → Grows sourceHeap before.native.machine.heap →
      SourceEqualityConstraintMemoAllocation.Valid before.operations →
      InputsThrough fuel (.code (.edge request .pure)) before →
      SourceEqualityNativeDemandOperations.FieldsThrough fuel (.code (.edge request .pure)) before →
      Returned (NodeResult target expected) before.native.nodes → Returned MismatchResult before.native.edges →
      (Returned (NodeResult target expected) (execute fuel (.code (.edge request .pure)) before).state.native.nodes ∧
        Returned MismatchResult (execute fuel (.code (.edge request .pure)) before).state.native.edges) ∧
      (∀ (count : Nat) (value : EdgeValue Symbol Guard) (after : Checked width), count ≤ fuel →
        Steps count (.code (.edge request .pure)) before (.code (.pure value)) after →
        MismatchResult request value)) := by
  refine SourceCurrentAllocatedNativeSourceQueryInduction.query_returned_and_raw_results
    (NodeResult target expected) MismatchResult sourceHeap ?_ ?_ fuel
  · intro request before bodyState middle parentFuel bodySteps value next
      physical _growth _valid plan _fields entered _firstGrowth _firstValid smaller actual nodeCalls _edgeCalls
    constructor
    · constructor
      · apply SourceCurrentAllocatedNativeRawBodyResults.compile_node_closed_self_trace_result
          request before bodyState middle parentFuel bodySteps value next entered smaller actual
        intro childSteps _small childNext childValue childAfter childEntry childTrace closed
        exact (nodeCalls ⟨IntersectionEmptyDomain.emptyDomain, request.left, request.left⟩
          childNext bodyState childAfter 1 childSteps childValue (by decide) (by omega)
          childEntry childTrace).1.1 rfl closed
      · exact SourceCurrentAllocatedNativePureQueryLaw.raw_result
          request bodyState middle bodySteps value actual
    · intro same
      subst request
      have reached := SourceCurrentAllocatedNativePrefixInputs.prefix_inputs_before_bind
        parentFuel 1 (.code (.node target .pure)) (.code (compileNode target)) next
        before bodyState physical plan entered (by omega)
      let allocated := SourceRecursiveIntersectionEnvironment.enter bodyState.native.machine.domains
        target.domain.key target.left target.right firstId secondId
      let started : Checked width :=
        {bodyState with native := advance bodyState.native {bodyState.native.machine with domains := allocated.2}}
      have canonical : compileNode ⟨allocated.1,
          SourceRecursiveIntersectionKernel.body target.left,
          SourceRecursiveIntersectionKernel.body target.right⟩ = .pure expected :=
        childPure bodyState.native.machine.domains reached.2.1.machine.2
      have result := SourceCurrentAllocatedNativeRawMuCutoffReplay.left_mu_cutoff_trace_result
        target before bodyState middle parentFuel bodySteps value expected firstId secondId next
        selected leftIdentity rightIdentity canonical absent entered smaller actual (by
          dsimp only
          intro used count positive bounded _small childNext childValue childAfter childEntry childTrace pure
          exact (nodeCalls ⟨allocated.1,
              SourceRecursiveIntersectionKernel.body target.left,
              SourceRecursiveIntersectionKernel.body target.right⟩
            childNext started childAfter used count childValue positive bounded childEntry childTrace).1.2
              expected pure)
      exact result.1
  · intro request before first middle parentFuel bodySteps value next
      physical _growth _valid plan _fields entered _firstGrowth _firstValid smaller actual _nodeCalls _edgeCalls mismatch
    have reached := SourceCurrentAllocatedNativePrefixInputs.prefix_inputs_before_bind
      parentFuel 1 (.code (.edge request .pure)) (.edgeBody request .pure) next
      before first physical plan entered (by omega)
    exact (SourceCurrentAllocatedNativeRawBodyResults.mismatch_edge_body_trace_result
      request first middle bodySteps value reached.2.1 mismatch actual).1

/-- The same original-budget query retains the Mu cutoff and all previous top-row laws. -/
theorem query_returned_and_raw_results
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (target : NodeRequest Symbol Guard) (expected : Value Symbol Guard) (firstId secondId : Nat)
    (selected : SourceRecursiveIntersectionControl.decision target.domain.key target.left target.right = .leftMu)
    (leftIdentity : SourceRecursiveIntersectionControl.identity target.left = some firstId)
    (rightIdentity : SourceRecursiveIntersectionControl.identity target.right = some secondId)
    (childPure : ∀ current : Cache.State IntersectionFlatMemoKeyDomain.DomainKey, Cache.Valid current →
      compileNode ⟨(SourceRecursiveIntersectionEnvironment.enter current target.domain.key
        target.left target.right firstId secondId).1,
        SourceRecursiveIntersectionKernel.body target.left,
        SourceRecursiveIntersectionKernel.body target.right⟩ = .pure expected)
    (absent : let binder := SourceRecursiveIntersectionControl.pair firstId secondId
      InternedBinderProtocol.Reference.intersection binder.1 binder.2 ∉ expected.free)
    (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (fuel : Nat) :
    (∀ (request : NodeRequest Symbol Guard) (before : Checked width),
      Physical before.native → Grows sourceHeap before.native.machine.heap →
      SourceEqualityConstraintMemoAllocation.Valid before.operations →
      InputsThrough fuel (.code (.node request .pure)) before →
      SourceEqualityNativeDemandOperations.FieldsThrough fuel (.code (.node request .pure)) before →
      Returned (NodeResult target expected) before.native.nodes → Returned EdgeResult before.native.edges →
      (Returned (NodeResult target expected) (execute fuel (.code (.node request .pure)) before).state.native.nodes ∧
        Returned EdgeResult (execute fuel (.code (.node request .pure)) before).state.native.edges) ∧
      (∀ (count : Nat) (value : Value Symbol Guard) (after : Checked width), count ≤ fuel →
        Steps count (.code (.node request .pure)) before (.code (.pure value)) after →
        NodeResult target expected request value)) ∧
    (∀ (request : EdgeRequest Symbol Guard) (before : Checked width),
      Physical before.native → Grows sourceHeap before.native.machine.heap →
      SourceEqualityConstraintMemoAllocation.Valid before.operations →
      InputsThrough fuel (.code (.edge request .pure)) before →
      SourceEqualityNativeDemandOperations.FieldsThrough fuel (.code (.edge request .pure)) before →
      Returned (NodeResult target expected) before.native.nodes → Returned EdgeResult before.native.edges →
      (Returned (NodeResult target expected) (execute fuel (.code (.edge request .pure)) before).state.native.nodes ∧
        Returned EdgeResult (execute fuel (.code (.edge request .pure)) before).state.native.edges) ∧
      (∀ (count : Nat) (value : EdgeValue Symbol Guard) (after : Checked width), count ≤ fuel →
        Steps count (.code (.edge request .pure)) before (.code (.pure value)) after →
        EdgeResult request value)) := by
  constructor
  · intro request before physical sourceGrowth valid plan fields nodes edges
    have oldNodes : Returned SourceCurrentAllocatedNativePureQueryGlobalLaws.NodeResult
        before.native.nodes := by
      intro handle old value stored
      exact (nodes handle old value stored).1
    have mismatchEdges : Returned MismatchResult before.native.edges := by
      intro handle old value stored
      exact (edges handle old value stored).1
    have refined := (cutoff_and_mismatch target expected firstId secondId selected leftIdentity rightIdentity childPure absent
      sourceHeap fuel).1 request before physical sourceGrowth valid plan fields nodes mismatchEdges
    have previous := (SourceCurrentAllocatedNativeTopRowQueryGlobalLaws.query_returned_and_raw_results
      sourceHeap fuel).1 request before physical sourceGrowth valid plan fields oldNodes edges
    exact ⟨⟨refined.1.1, previous.1.2⟩, refined.2⟩
  · intro request before physical sourceGrowth valid plan fields nodes edges
    have oldNodes : Returned SourceCurrentAllocatedNativePureQueryGlobalLaws.NodeResult
        before.native.nodes := by
      intro handle old value stored
      exact (nodes handle old value stored).1
    have mismatchEdges : Returned MismatchResult before.native.edges := by
      intro handle old value stored
      exact (edges handle old value stored).1
    have refined := (cutoff_and_mismatch target expected firstId secondId selected leftIdentity rightIdentity childPure absent
      sourceHeap fuel).2 request before physical sourceGrowth valid plan fields nodes mismatchEdges
    have previous := (SourceCurrentAllocatedNativeTopRowQueryGlobalLaws.query_returned_and_raw_results
      sourceHeap fuel).2 request before physical sourceGrowth valid plan fields oldNodes edges
    exact ⟨⟨refined.1.1, previous.1.2⟩, previous.2⟩

/-- Both actual initial memo tables supply the complete node and edge laws. -/
theorem initial_node_query_returned_and_raw_results
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (target : NodeRequest Symbol Guard) (expected : Value Symbol Guard) (firstId secondId : Nat)
    (selected : SourceRecursiveIntersectionControl.decision target.domain.key target.left target.right = .leftMu)
    (leftIdentity : SourceRecursiveIntersectionControl.identity target.left = some firstId)
    (rightIdentity : SourceRecursiveIntersectionControl.identity target.right = some secondId)
    (childPure : ∀ current : Cache.State IntersectionFlatMemoKeyDomain.DomainKey, Cache.Valid current →
      compileNode ⟨(SourceRecursiveIntersectionEnvironment.enter current target.domain.key
        target.left target.right firstId secondId).1,
        SourceRecursiveIntersectionKernel.body target.left,
        SourceRecursiveIntersectionKernel.body target.right⟩ = .pure expected)
    (absent : let binder := SourceRecursiveIntersectionControl.pair firstId secondId
      InternedBinderProtocol.Reference.intersection binder.1 binder.2 ∉ expected.free)
    (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (machine : SourceRecursiveIntersectionKernel.Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid machine)
    (sourceGrowth : Grows sourceHeap machine.heap)
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid operations)
    (fuel : Nat) (request : NodeRequest Symbol Guard)
    (plan : InputsThrough fuel (.code (.node request .pure)) ⟨initial width machine, operations⟩)
    (fields : FieldsThrough fuel (.code (.node request .pure)) ⟨initial width machine, operations⟩) :
    (Returned (NodeResult target expected) (execute fuel (.code (.node request .pure))
      ⟨initial width machine, operations⟩).state.native.nodes ∧
      Returned EdgeResult (execute fuel (.code (.node request .pure))
        ⟨initial width machine, operations⟩).state.native.edges) ∧
    (∀ (count : Nat) (value : Value Symbol Guard) (after : Checked width), count ≤ fuel →
      Steps count (.code (.node request .pure)) ⟨initial width machine, operations⟩ (.code (.pure value)) after →
      NodeResult target expected request value) := by
  exact (query_returned_and_raw_results target expected firstId secondId selected leftIdentity rightIdentity childPure absent sourceHeap fuel).1
    request ⟨initial width machine, operations⟩
    (SourceCurrentAllocatedNativePhysicalCache.initial_valid machine valid)
    sourceGrowth operationsValid plan fields
    (SourceCurrentAllocatedNativeContextCache.returned_empty (NodeResult target expected))
    (SourceCurrentAllocatedNativeContextCache.returned_empty EdgeResult)

/-- Both actual initial memo tables supply the complete node and edge laws. -/
theorem initial_edge_query_returned_and_raw_results
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (target : NodeRequest Symbol Guard) (expected : Value Symbol Guard) (firstId secondId : Nat)
    (selected : SourceRecursiveIntersectionControl.decision target.domain.key target.left target.right = .leftMu)
    (leftIdentity : SourceRecursiveIntersectionControl.identity target.left = some firstId)
    (rightIdentity : SourceRecursiveIntersectionControl.identity target.right = some secondId)
    (childPure : ∀ current : Cache.State IntersectionFlatMemoKeyDomain.DomainKey, Cache.Valid current →
      compileNode ⟨(SourceRecursiveIntersectionEnvironment.enter current target.domain.key
        target.left target.right firstId secondId).1,
        SourceRecursiveIntersectionKernel.body target.left,
        SourceRecursiveIntersectionKernel.body target.right⟩ = .pure expected)
    (absent : let binder := SourceRecursiveIntersectionControl.pair firstId secondId
      InternedBinderProtocol.Reference.intersection binder.1 binder.2 ∉ expected.free)
    (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (machine : SourceRecursiveIntersectionKernel.Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid machine)
    (sourceGrowth : Grows sourceHeap machine.heap)
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid operations)
    (fuel : Nat) (request : EdgeRequest Symbol Guard)
    (plan : InputsThrough fuel (.code (.edge request .pure)) ⟨initial width machine, operations⟩)
    (fields : FieldsThrough fuel (.code (.edge request .pure)) ⟨initial width machine, operations⟩) :
    (Returned (NodeResult target expected) (execute fuel (.code (.edge request .pure))
      ⟨initial width machine, operations⟩).state.native.nodes ∧
      Returned EdgeResult (execute fuel (.code (.edge request .pure))
        ⟨initial width machine, operations⟩).state.native.edges) ∧
    (∀ (count : Nat) (value : EdgeValue Symbol Guard) (after : Checked width), count ≤ fuel →
      Steps count (.code (.edge request .pure)) ⟨initial width machine, operations⟩ (.code (.pure value)) after →
      EdgeResult request value) := by
  exact (query_returned_and_raw_results target expected firstId secondId selected leftIdentity rightIdentity childPure absent sourceHeap fuel).2
    request ⟨initial width machine, operations⟩
    (SourceCurrentAllocatedNativePhysicalCache.initial_valid machine valid)
    sourceGrowth operationsValid plan fields
    (SourceCurrentAllocatedNativeContextCache.returned_empty (NodeResult target expected))
    (SourceCurrentAllocatedNativeContextCache.returned_empty EdgeResult)

end MicroCFTA.SourceCurrentAllocatedNativeMuCutoffQueryGlobalLaws
