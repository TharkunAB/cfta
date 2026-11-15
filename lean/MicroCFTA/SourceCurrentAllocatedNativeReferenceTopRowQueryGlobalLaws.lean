import MicroCFTA.SourceCurrentAllocatedNativeSourceQueryInduction
import MicroCFTA.SourceCurrentAllocatedNativeReferenceCutoffQueryGlobalLaws
import MicroCFTA.SourceCurrentAllocatedNativeTopRowBodyReadback

/-!
# Ordered top-row history through selected Mu and reference children

Known child syntax includes the checked nonterminal Mu and reference cuts.
The existing complete node predicate stays unchanged.
Actual smaller child results fix the complete ordered row and full key.
Both native memo tables start empty in the initial corollaries.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeReferenceTopRowQueryGlobalLaws
open Cache InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeContextCache (Returned)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
open SourceCurrentAllocatedNativeQueryGlobalLaws (MismatchResult)
open SourceCurrentAllocatedNativeReferenceCutoffQueryGlobalLaws (NodeResult)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid
variable {width : Nat}

set_option autoImplicit false

def KnownResult [DecidableEq Symbol] (muTarget referenceTarget : NodeRequest Symbol Guard)
    (cutoff : Value Symbol Guard) (request : NodeRequest Symbol Guard)
    (wanted : Value Symbol Guard) : Prop :=
  SourceCurrentAllocatedNativeTopRowQueryGlobalLaws.KnownResult request wanted ∨
    ((request = muTarget ∨ request = referenceTarget) ∧ wanted = cutoff)

def TopRowResult [DecidableEq Symbol] (muTarget referenceTarget : NodeRequest Symbol Guard)
    (cutoff : Value Symbol Guard) (request : EdgeRequest Symbol Guard)
    (row : EdgeValue Symbol Guard) : Prop :=
  request.right = request.left →
  request.left.entry.key.constraint = SourceEqualityConstraintConstructors.top →
  ∀ expected : List (Value Symbol Guard),
    Language.All₂ (fun (pair : Value Symbol Guard × Value Symbol Guard) (value : Value Symbol Guard) =>
      KnownResult muTarget referenceTarget cutoff ⟨request.domain, pair.1, pair.2⟩ value)
      (request.left.children.zip request.right.children) expected →
    row.children = expected ∧
      row.entry.key = ⟨request.left.entry.key.symbol, expected.map Value.referenceOf,
        SourceEqualityConstraintConstructors.top⟩

def EdgeResult [DecidableEq Symbol] (muTarget referenceTarget : NodeRequest Symbol Guard)
    (cutoff : Value Symbol Guard) (request : EdgeRequest Symbol Guard)
    (row : EdgeValue Symbol Guard) : Prop :=
  MismatchResult request row ∧ TopRowResult muTarget referenceTarget cutoff request row

private theorem known_result [DecidableEq Symbol]
    (muTarget referenceTarget : NodeRequest Symbol Guard) (cutoff : Value Symbol Guard)
    (request : NodeRequest Symbol Guard) (value wanted : Value Symbol Guard)
    (actual : NodeResult muTarget referenceTarget cutoff request value)
    (known : KnownResult muTarget referenceTarget cutoff request wanted) : value = wanted := by
  rcases known with previous | ⟨selected, same⟩
  · rcases previous with ⟨self, closed, expected⟩ | pure
    · exact (actual.1.1.1 self closed).trans expected.symm
    · exact actual.1.1.2 wanted pure
  · rcases selected with mu | reference
    · exact (actual.1.2 mu).trans same.symm
    · exact (actual.2 reference).trans same.symm

private theorem ordered_values [DecidableEq Symbol]
    (muTarget referenceTarget : NodeRequest Symbol Guard) (cutoff : Value Symbol Guard)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    {pairs : List (Value Symbol Guard × Value Symbol Guard)}
    {values expected : List (Value Symbol Guard)}
    (actual : Language.All₂ (fun pair value => ∀ wanted,
      KnownResult muTarget referenceTarget cutoff ⟨domain, pair.1, pair.2⟩ wanted →
        value = wanted) pairs values)
    (selected : Language.All₂ (fun pair value =>
      KnownResult muTarget referenceTarget cutoff ⟨domain, pair.1, pair.2⟩ value) pairs expected) :
    values = expected := by
  induction selected generalizing values with
  | nil => cases actual; rfl
  | cons chosen tail ih =>
      cases actual with
      | cons result rest => rw [result _ chosen, ih rest]

/-- Original-budget history retains exact ordered rows through all known child clauses. -/
theorem query_returned_and_raw_results
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (muTarget referenceTarget : NodeRequest Symbol Guard) (expected : Value Symbol Guard) (firstId secondId : Nat)
    (selected : SourceRecursiveIntersectionControl.decision muTarget.domain.key muTarget.left muTarget.right = .leftMu)
    (leftIdentity : SourceRecursiveIntersectionControl.identity muTarget.left = some firstId)
    (rightIdentity : SourceRecursiveIntersectionControl.identity muTarget.right = some secondId)
    (childPure : ∀ current : Cache.State IntersectionFlatMemoKeyDomain.DomainKey, Cache.Valid current →
      compileNode ⟨(SourceRecursiveIntersectionEnvironment.enter current muTarget.domain.key
        muTarget.left muTarget.right firstId secondId).1,
        SourceRecursiveIntersectionKernel.body muTarget.left,
        SourceRecursiveIntersectionKernel.body muTarget.right⟩ = .pure expected)
    (absent : let binder := SourceRecursiveIntersectionControl.pair firstId secondId
      InternedBinderProtocol.Reference.intersection binder.1 binder.2 ∉ expected.free)
    (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (read : ∀ current : Checked width, Physical current.native →
      Grows sourceHeap current.native.machine.heap →
      SourceEqualityNativeDemand.step (.code (compileNode referenceTarget)) current =
        .yielded (.code (requestNode muTarget.domain muTarget.left muTarget.right)) current)
    (fuel : Nat) :
    (∀ (request : NodeRequest Symbol Guard) (before : Checked width),
      Physical before.native → Grows sourceHeap before.native.machine.heap →
      SourceEqualityConstraintMemoAllocation.Valid before.operations →
      InputsThrough fuel (.code (.node request .pure)) before →
      SourceEqualityNativeDemandOperations.FieldsThrough fuel (.code (.node request .pure)) before →
      Returned (NodeResult muTarget referenceTarget expected) before.native.nodes → Returned (EdgeResult muTarget referenceTarget expected) before.native.edges →
      (Returned (NodeResult muTarget referenceTarget expected) (execute fuel (.code (.node request .pure)) before).state.native.nodes ∧
        Returned (EdgeResult muTarget referenceTarget expected) (execute fuel (.code (.node request .pure)) before).state.native.edges) ∧
      (∀ (count : Nat) (value : Value Symbol Guard) (after : Checked width), count ≤ fuel →
        Steps count (.code (.node request .pure)) before (.code (.pure value)) after →
        NodeResult muTarget referenceTarget expected request value)) ∧
    (∀ (request : EdgeRequest Symbol Guard) (before : Checked width),
      Physical before.native → Grows sourceHeap before.native.machine.heap →
      SourceEqualityConstraintMemoAllocation.Valid before.operations →
      InputsThrough fuel (.code (.edge request .pure)) before →
      SourceEqualityNativeDemandOperations.FieldsThrough fuel (.code (.edge request .pure)) before →
      Returned (NodeResult muTarget referenceTarget expected) before.native.nodes → Returned (EdgeResult muTarget referenceTarget expected) before.native.edges →
      (Returned (NodeResult muTarget referenceTarget expected) (execute fuel (.code (.edge request .pure)) before).state.native.nodes ∧
        Returned (EdgeResult muTarget referenceTarget expected) (execute fuel (.code (.edge request .pure)) before).state.native.edges) ∧
      (∀ (count : Nat) (value : EdgeValue Symbol Guard) (after : Checked width), count ≤ fuel →
        Steps count (.code (.edge request .pure)) before (.code (.pure value)) after →
        EdgeResult muTarget referenceTarget expected request value)) := by
  refine SourceCurrentAllocatedNativeSourceQueryInduction.query_returned_and_raw_results
    (NodeResult muTarget referenceTarget expected) (EdgeResult muTarget referenceTarget expected)
    sourceHeap ?_ ?_ fuel
  · intro request before bodyState middle parentFuel bodySteps value next
      physical _growth _valid plan _fields entered firstGrowth _firstValid smaller actual nodeCalls _edgeCalls
    constructor
    · constructor
      · constructor
        · apply SourceCurrentAllocatedNativeRawBodyResults.compile_node_closed_self_trace_result
            request before bodyState middle parentFuel bodySteps value next entered smaller actual
          intro childSteps _small childNext childValue childAfter childEntry childTrace closed
          exact (nodeCalls ⟨IntersectionEmptyDomain.emptyDomain, request.left, request.left⟩
            childNext bodyState childAfter 1 childSteps childValue (by decide) (by omega)
            childEntry childTrace).1.1.1 rfl closed
        · exact SourceCurrentAllocatedNativePureQueryLaw.raw_result
            request bodyState middle bodySteps value actual
      · intro same
        subst request
        have reached := SourceCurrentAllocatedNativePrefixInputs.prefix_inputs_before_bind
          parentFuel 1 (.code (.node muTarget .pure)) (.code (compileNode muTarget)) next
          before bodyState physical plan entered (by omega)
        let allocated := SourceRecursiveIntersectionEnvironment.enter bodyState.native.machine.domains
          muTarget.domain.key muTarget.left muTarget.right firstId secondId
        let started : Checked width :=
          {bodyState with native := advance bodyState.native {bodyState.native.machine with domains := allocated.2}}
        have canonical : compileNode ⟨allocated.1,
            SourceRecursiveIntersectionKernel.body muTarget.left,
            SourceRecursiveIntersectionKernel.body muTarget.right⟩ = .pure expected :=
          childPure bodyState.native.machine.domains reached.2.1.machine.2
        have result := SourceCurrentAllocatedNativeRawMuCutoffReplay.left_mu_cutoff_trace_result
          muTarget before bodyState middle parentFuel bodySteps value expected firstId secondId next
          selected leftIdentity rightIdentity canonical absent entered smaller actual (by
            dsimp only
            intro used count positive bounded _small childNext childValue childAfter childEntry childTrace pure
            exact (nodeCalls ⟨allocated.1,
                SourceRecursiveIntersectionKernel.body muTarget.left,
                SourceRecursiveIntersectionKernel.body muTarget.right⟩
              childNext started childAfter used count childValue positive bounded childEntry childTrace).1.1.2
                expected pure)
        exact result.1
    · intro same
      subst request
      have reached := SourceCurrentAllocatedNativePrefixInputs.prefix_inputs_before_bind
        parentFuel 1 (.code (.node referenceTarget .pure)) (.code (compileNode referenceTarget)) next
        before bodyState physical plan entered (by omega)
      have actualRead := read bodyState reached.2.1 firstGrowth
      have result := SourceCurrentAllocatedNativeRawReferenceReplay.reference_trace_result_of_actual_read
        referenceTarget muTarget before bodyState middle parentFuel bodySteps value expected next
        actualRead entered smaller actual (by
          intro used count positive bounded _small childNext childValue childAfter childEntry childTrace
          exact (nodeCalls muTarget childNext bodyState childAfter used count childValue
            positive bounded childEntry childTrace).1.2 rfl)
      exact result.1
  · intro request before first middle parentFuel bodySteps value next
      physical _growth _valid plan _fields entered _firstGrowth firstValid smaller actual nodeCalls _edgeCalls
    have reached := SourceCurrentAllocatedNativePrefixInputs.prefix_inputs_before_bind
      parentFuel 1 (.code (.edge request .pure)) (.edgeBody request .pure) next
      before first physical plan entered (by omega)
    constructor
    · intro mismatch
      exact (SourceCurrentAllocatedNativeRawBodyResults.mismatch_edge_body_trace_result
        request first middle bodySteps value reached.2.1 mismatch actual).1
    · intro self sourceTop wanted selectedChildren
      have readback := SourceCurrentAllocatedNativeTopRowBodyReadback.self_top_body_readback_of_smaller_nodes
        (fun pair result => ∀ selectedValue,
          KnownResult muTarget referenceTarget expected ⟨request.domain, pair.1, pair.2⟩ selectedValue →
            result = selectedValue)
        request before first middle parentFuel bodySteps value next self sourceTop
        reached.2.1 firstValid entered smaller reached.2.2.2.2 actual (by
          intro used count positive bounded _small pair _member childNext childBefore childAfter childValue
            origin _childPhysical childTrace selectedValue known
          have property := nodeCalls ⟨request.domain, pair.1, pair.2⟩ childNext childBefore childAfter
            used count childValue positive bounded origin childTrace
          exact known_result muTarget referenceTarget expected
            ⟨request.domain, pair.1, pair.2⟩ childValue selectedValue property known)
      have same := ordered_values muTarget referenceTarget expected request.domain readback.1 selectedChildren
      exact ⟨same, by simpa only [same] using readback.2.1⟩

/-- Both actual initial memo tables supply the complete node and stronger row laws. -/
theorem initial_node_query_returned_and_raw_results
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (muTarget referenceTarget : NodeRequest Symbol Guard) (expected : Value Symbol Guard) (firstId secondId : Nat)
    (selected : SourceRecursiveIntersectionControl.decision muTarget.domain.key muTarget.left muTarget.right = .leftMu)
    (leftIdentity : SourceRecursiveIntersectionControl.identity muTarget.left = some firstId)
    (rightIdentity : SourceRecursiveIntersectionControl.identity muTarget.right = some secondId)
    (childPure : ∀ current : Cache.State IntersectionFlatMemoKeyDomain.DomainKey, Cache.Valid current →
      compileNode ⟨(SourceRecursiveIntersectionEnvironment.enter current muTarget.domain.key
        muTarget.left muTarget.right firstId secondId).1,
        SourceRecursiveIntersectionKernel.body muTarget.left,
        SourceRecursiveIntersectionKernel.body muTarget.right⟩ = .pure expected)
    (absent : let binder := SourceRecursiveIntersectionControl.pair firstId secondId
      InternedBinderProtocol.Reference.intersection binder.1 binder.2 ∉ expected.free)
    (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (read : ∀ current : Checked width, Physical current.native →
      Grows sourceHeap current.native.machine.heap →
      SourceEqualityNativeDemand.step (.code (compileNode referenceTarget)) current =
        .yielded (.code (requestNode muTarget.domain muTarget.left muTarget.right)) current)
    (machine : SourceRecursiveIntersectionKernel.Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid machine)
    (sourceGrowth : Grows sourceHeap machine.heap)
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid operations)
    (fuel : Nat) (request : NodeRequest Symbol Guard)
    (plan : InputsThrough fuel (.code (.node request .pure)) ⟨initial width machine, operations⟩)
    (fields : FieldsThrough fuel (.code (.node request .pure)) ⟨initial width machine, operations⟩) :
    (Returned (NodeResult muTarget referenceTarget expected) (execute fuel (.code (.node request .pure))
      ⟨initial width machine, operations⟩).state.native.nodes ∧
      Returned (EdgeResult muTarget referenceTarget expected) (execute fuel (.code (.node request .pure))
        ⟨initial width machine, operations⟩).state.native.edges) ∧
    (∀ (count : Nat) (value : Value Symbol Guard) (after : Checked width), count ≤ fuel →
      Steps count (.code (.node request .pure)) ⟨initial width machine, operations⟩ (.code (.pure value)) after →
      NodeResult muTarget referenceTarget expected request value) := by
  exact (query_returned_and_raw_results muTarget referenceTarget expected firstId secondId selected leftIdentity rightIdentity childPure absent
    sourceHeap read fuel).1 request ⟨initial width machine, operations⟩
    (SourceCurrentAllocatedNativePhysicalCache.initial_valid machine valid)
    sourceGrowth operationsValid plan fields
    (SourceCurrentAllocatedNativeContextCache.returned_empty (NodeResult muTarget referenceTarget expected))
    (SourceCurrentAllocatedNativeContextCache.returned_empty (EdgeResult muTarget referenceTarget expected))

/-- Both actual initial memo tables supply the complete node and stronger row laws. -/
theorem initial_edge_query_returned_and_raw_results
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (muTarget referenceTarget : NodeRequest Symbol Guard) (expected : Value Symbol Guard) (firstId secondId : Nat)
    (selected : SourceRecursiveIntersectionControl.decision muTarget.domain.key muTarget.left muTarget.right = .leftMu)
    (leftIdentity : SourceRecursiveIntersectionControl.identity muTarget.left = some firstId)
    (rightIdentity : SourceRecursiveIntersectionControl.identity muTarget.right = some secondId)
    (childPure : ∀ current : Cache.State IntersectionFlatMemoKeyDomain.DomainKey, Cache.Valid current →
      compileNode ⟨(SourceRecursiveIntersectionEnvironment.enter current muTarget.domain.key
        muTarget.left muTarget.right firstId secondId).1,
        SourceRecursiveIntersectionKernel.body muTarget.left,
        SourceRecursiveIntersectionKernel.body muTarget.right⟩ = .pure expected)
    (absent : let binder := SourceRecursiveIntersectionControl.pair firstId secondId
      InternedBinderProtocol.Reference.intersection binder.1 binder.2 ∉ expected.free)
    (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (read : ∀ current : Checked width, Physical current.native →
      Grows sourceHeap current.native.machine.heap →
      SourceEqualityNativeDemand.step (.code (compileNode referenceTarget)) current =
        .yielded (.code (requestNode muTarget.domain muTarget.left muTarget.right)) current)
    (machine : SourceRecursiveIntersectionKernel.Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid machine)
    (sourceGrowth : Grows sourceHeap machine.heap)
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid operations)
    (fuel : Nat) (request : EdgeRequest Symbol Guard)
    (plan : InputsThrough fuel (.code (.edge request .pure)) ⟨initial width machine, operations⟩)
    (fields : FieldsThrough fuel (.code (.edge request .pure)) ⟨initial width machine, operations⟩) :
    (Returned (NodeResult muTarget referenceTarget expected) (execute fuel (.code (.edge request .pure))
      ⟨initial width machine, operations⟩).state.native.nodes ∧
      Returned (EdgeResult muTarget referenceTarget expected) (execute fuel (.code (.edge request .pure))
        ⟨initial width machine, operations⟩).state.native.edges) ∧
    (∀ (count : Nat) (value : EdgeValue Symbol Guard) (after : Checked width), count ≤ fuel →
      Steps count (.code (.edge request .pure)) ⟨initial width machine, operations⟩ (.code (.pure value)) after →
      EdgeResult muTarget referenceTarget expected request value) := by
  exact (query_returned_and_raw_results muTarget referenceTarget expected firstId secondId selected leftIdentity rightIdentity childPure absent
    sourceHeap read fuel).2 request ⟨initial width machine, operations⟩
    (SourceCurrentAllocatedNativePhysicalCache.initial_valid machine valid)
    sourceGrowth operationsValid plan fields
    (SourceCurrentAllocatedNativeContextCache.returned_empty (NodeResult muTarget referenceTarget expected))
    (SourceCurrentAllocatedNativeContextCache.returned_empty (EdgeResult muTarget referenceTarget expected))

end MicroCFTA.SourceCurrentAllocatedNativeReferenceTopRowQueryGlobalLaws
