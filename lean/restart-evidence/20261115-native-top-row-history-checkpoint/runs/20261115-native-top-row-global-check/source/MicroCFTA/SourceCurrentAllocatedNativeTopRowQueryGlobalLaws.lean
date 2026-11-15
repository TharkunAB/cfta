import MicroCFTA.SourceCurrentAllocatedNativeSourceQueryInduction
import MicroCFTA.SourceCurrentAllocatedNativePureQueryGlobalLaws
import MicroCFTA.SourceCurrentAllocatedNativeTopRowBodyReadback

/-!
# Exact matching top rows from initialized native history

The same returned laws retain closed-self and literal pure node results.
Matching top rows retain their prescribed ordered shortcut children.
Source growth and valid operations follow the actual original prefixes.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeTopRowQueryGlobalLaws
open Cache InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeContextCache (Returned)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
open SourceCurrentAllocatedNativePureQueryGlobalLaws (NodeResult)
open SourceCurrentAllocatedNativeQueryGlobalLaws (MismatchResult)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid
variable {width : Nat}
set_option autoImplicit false

/-- A closed self shortcut or literal pure branch fixes the expected complete value. -/
def KnownResult [DecidableEq Symbol] (request : NodeRequest Symbol Guard)
    (expected : Value Symbol Guard) : Prop :=
  (request.right = request.left ∧ request.left.free = [] ∧ expected = request.left) ∨
    compileNode request = .pure expected

/-- A matching source top row retains the prescribed ordered shortcut child results and full key. -/
def TopRowResult [DecidableEq Symbol] (request : EdgeRequest Symbol Guard)
    (row : EdgeValue Symbol Guard) : Prop :=
  request.right = request.left →
  request.left.entry.key.constraint = SourceEqualityConstraintConstructors.top →
  ∀ expected : List (Value Symbol Guard),
    Language.All₂ (fun (pair : Value Symbol Guard × Value Symbol Guard) (value : Value Symbol Guard) => KnownResult ⟨request.domain, pair.1, pair.2⟩ value)
      (request.left.children.zip request.right.children) expected →
    row.children = expected ∧
      row.entry.key = ⟨request.left.entry.key.symbol, expected.map Value.referenceOf,
        SourceEqualityConstraintConstructors.top⟩
/-- The same edge cells retain mismatch sentinels and exact matching top rows. -/
def EdgeResult [DecidableEq Symbol] (request : EdgeRequest Symbol Guard)
    (row : EdgeValue Symbol Guard) : Prop :=
  MismatchResult request row ∧ TopRowResult request row

private theorem known_result [DecidableEq Symbol]
    (request : NodeRequest Symbol Guard) (value expected : Value Symbol Guard)
    (actual : NodeResult request value) (known : KnownResult request expected) :
    value = expected := by
  rcases known with ⟨self, closed, same⟩ | selected
  · exact (actual.1 self closed).trans same.symm
  · exact actual.2 expected selected

private theorem ordered_values [DecidableEq Symbol]
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    {pairs : List (Value Symbol Guard × Value Symbol Guard)}
    {values expected : List (Value Symbol Guard)}
    (actual : Language.All₂ (fun pair value => ∀ wanted,
      KnownResult ⟨domain, pair.1, pair.2⟩ wanted → value = wanted) pairs values)
    (selected : Language.All₂ (fun pair value => KnownResult ⟨domain, pair.1, pair.2⟩ value)
      pairs expected) : values = expected := by
  induction selected generalizing values with
  | nil => cases actual; rfl
  | cons chosen tail ih =>
      cases actual with
      | cons result rest => exact congrArg₂ List.cons (result _ chosen) (ih rest)

/-- Original-budget query history retains exact node shortcuts and matching top-row keys. -/
theorem query_returned_and_raw_results
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (fuel : Nat) :
    (∀ (request : NodeRequest Symbol Guard) (before : Checked width),
      Physical before.native → Grows sourceHeap before.native.machine.heap →
      SourceEqualityConstraintMemoAllocation.Valid before.operations →
      InputsThrough fuel (.code (.node request .pure)) before →
      SourceEqualityNativeDemandOperations.FieldsThrough fuel (.code (.node request .pure)) before →
      Returned NodeResult before.native.nodes → Returned EdgeResult before.native.edges →
      (Returned NodeResult (execute fuel (.code (.node request .pure)) before).state.native.nodes ∧
        Returned EdgeResult (execute fuel (.code (.node request .pure)) before).state.native.edges) ∧
      (∀ (count : Nat) (value : Value Symbol Guard) (after : Checked width), count ≤ fuel →
        Steps count (.code (.node request .pure)) before (.code (.pure value)) after →
        NodeResult request value)) ∧
    (∀ (request : EdgeRequest Symbol Guard) (before : Checked width),
      Physical before.native → Grows sourceHeap before.native.machine.heap →
      SourceEqualityConstraintMemoAllocation.Valid before.operations →
      InputsThrough fuel (.code (.edge request .pure)) before →
      SourceEqualityNativeDemandOperations.FieldsThrough fuel (.code (.edge request .pure)) before →
      Returned NodeResult before.native.nodes → Returned EdgeResult before.native.edges →
      (Returned NodeResult (execute fuel (.code (.edge request .pure)) before).state.native.nodes ∧
        Returned EdgeResult (execute fuel (.code (.edge request .pure)) before).state.native.edges) ∧
      (∀ (count : Nat) (value : EdgeValue Symbol Guard) (after : Checked width), count ≤ fuel →
        Steps count (.code (.edge request .pure)) before (.code (.pure value)) after →
        EdgeResult request value)) := by
  refine SourceCurrentAllocatedNativeSourceQueryInduction.query_returned_and_raw_results
    NodeResult EdgeResult sourceHeap ?_ ?_ fuel
  · intro request before first middle parentFuel bodySteps value next
      physical _growth _valid plan _fields entered _firstGrowth _firstValid smaller actual nodeCalls _edgeCalls
    constructor
    · apply SourceCurrentAllocatedNativeRawBodyResults.compile_node_closed_self_trace_result
        request before first middle parentFuel bodySteps value next entered smaller actual
      intro childSteps _small childNext childValue childAfter childEntry childTrace closed
      exact (nodeCalls ⟨IntersectionEmptyDomain.emptyDomain, request.left, request.left⟩
        childNext first childAfter 1 childSteps childValue (by decide) (by omega)
        childEntry childTrace).1 rfl closed
    · exact SourceCurrentAllocatedNativePureQueryLaw.raw_result
        request first middle bodySteps value actual
  · intro request before first middle parentFuel bodySteps value next
      physical _growth _valid plan _fields entered _firstGrowth firstValid smaller actual nodeCalls _edgeCalls
    have reached := SourceCurrentAllocatedNativePrefixInputs.prefix_inputs_before_bind
      parentFuel 1 (.code (.edge request .pure)) (.edgeBody request .pure) next
      before first physical plan entered (by omega)
    constructor
    · intro mismatch
      exact (SourceCurrentAllocatedNativeRawBodyResults.mismatch_edge_body_trace_result
        request first middle bodySteps value reached.2.1 mismatch actual).1
    · intro self sourceTop expected selected
      have readback := SourceCurrentAllocatedNativeTopRowBodyReadback.self_top_body_readback_of_smaller_nodes
        (fun pair result => ∀ wanted, KnownResult ⟨request.domain, pair.1, pair.2⟩ wanted → result = wanted)
        request before first middle parentFuel bodySteps value next self sourceTop
        reached.2.1 firstValid entered smaller reached.2.2.2.2 actual (by
          intro used count positive bounded _small pair _member childNext childBefore childAfter childValue
            origin _childPhysical childTrace wanted known
          have property := nodeCalls ⟨request.domain, pair.1, pair.2⟩ childNext childBefore childAfter
            used count childValue positive bounded origin childTrace
          exact known_result ⟨request.domain, pair.1, pair.2⟩ childValue wanted property known)
      have same := ordered_values request.domain readback.1 selected
      exact ⟨same, by simpa only [same] using readback.2.1⟩

/-- Actual empty memo initialization supplies both row and node laws at every endpoint. -/
theorem initial_node_query_returned_and_raw_results
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (machine : SourceRecursiveIntersectionKernel.Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid machine)
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid operations)
    (fuel : Nat) (request : NodeRequest Symbol Guard)
    (plan : InputsThrough fuel (.code (.node request .pure)) ⟨initial width machine, operations⟩)
    (fields : FieldsThrough fuel (.code (.node request .pure)) ⟨initial width machine, operations⟩) :
    (Returned NodeResult (execute fuel (.code (.node request .pure))
      ⟨initial width machine, operations⟩).state.native.nodes ∧
      Returned EdgeResult (execute fuel (.code (.node request .pure))
        ⟨initial width machine, operations⟩).state.native.edges) ∧
    (∀ (count : Nat) (value : Value Symbol Guard) (after : Checked width), count ≤ fuel →
      Steps count (.code (.node request .pure)) ⟨initial width machine, operations⟩ (.code (.pure value)) after →
      NodeResult request value) := by
  exact (query_returned_and_raw_results machine.heap fuel).1 request ⟨initial width machine, operations⟩
    (SourceCurrentAllocatedNativePhysicalCache.initial_valid machine valid)
    (InternedConstructorTemplates.grows_refl machine.heap) operationsValid plan fields
    (SourceCurrentAllocatedNativeContextCache.returned_empty NodeResult)
    (SourceCurrentAllocatedNativeContextCache.returned_empty EdgeResult)

/-- Actual empty memo initialization supplies both row and node laws at every endpoint. -/
theorem initial_edge_query_returned_and_raw_results
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (machine : SourceRecursiveIntersectionKernel.Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid machine)
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid operations)
    (fuel : Nat) (request : EdgeRequest Symbol Guard)
    (plan : InputsThrough fuel (.code (.edge request .pure)) ⟨initial width machine, operations⟩)
    (fields : FieldsThrough fuel (.code (.edge request .pure)) ⟨initial width machine, operations⟩) :
    (Returned NodeResult (execute fuel (.code (.edge request .pure))
      ⟨initial width machine, operations⟩).state.native.nodes ∧
      Returned EdgeResult (execute fuel (.code (.edge request .pure))
        ⟨initial width machine, operations⟩).state.native.edges) ∧
    (∀ (count : Nat) (value : EdgeValue Symbol Guard) (after : Checked width), count ≤ fuel →
      Steps count (.code (.edge request .pure)) ⟨initial width machine, operations⟩ (.code (.pure value)) after →
      EdgeResult request value) := by
  exact (query_returned_and_raw_results machine.heap fuel).2 request ⟨initial width machine, operations⟩
    (SourceCurrentAllocatedNativePhysicalCache.initial_valid machine valid)
    (InternedConstructorTemplates.grows_refl machine.heap) operationsValid plan fields
    (SourceCurrentAllocatedNativeContextCache.returned_empty NodeResult)
    (SourceCurrentAllocatedNativeContextCache.returned_empty EdgeResult)

end MicroCFTA.SourceCurrentAllocatedNativeTopRowQueryGlobalLaws

#check @MicroCFTA.SourceCurrentAllocatedNativeTopRowQueryGlobalLaws.query_returned_and_raw_results
#print axioms MicroCFTA.SourceCurrentAllocatedNativeTopRowQueryGlobalLaws.query_returned_and_raw_results
#check @MicroCFTA.SourceCurrentAllocatedNativeTopRowQueryGlobalLaws.initial_node_query_returned_and_raw_results
#print axioms MicroCFTA.SourceCurrentAllocatedNativeTopRowQueryGlobalLaws.initial_node_query_returned_and_raw_results
#check @MicroCFTA.SourceCurrentAllocatedNativeTopRowQueryGlobalLaws.initial_edge_query_returned_and_raw_results
#print axioms MicroCFTA.SourceCurrentAllocatedNativeTopRowQueryGlobalLaws.initial_edge_query_returned_and_raw_results
