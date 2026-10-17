import MicroCFTA.SourceCurrentParentNativeHistory
import MicroCFTA.SourceCurrentNativeWriterReadyRetention

/-!
# Native request lineage for actual shared leaves

A leaf forces its target before its checked native request. A slot hit
retains the historical target receipt. Completed native requests either
use the unresolved direct branch or retain their exact returned cell and
captured writer. Initial history derives the final writer history.
-/
namespace MicroCFTA.SourceCurrentSharedLeafNativeLineage
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativeSemanticTraceReadback (bind_inverse effects)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentNativeEdgeWriterGrowth (History)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Shared" => SourceCurrentAllocatedSharedTargetState.State
local notation "Inventory" => SourceCurrentAllocatedNativeInventoryState.Inventory
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
variable {width : Nat}

private theorem closed_key (input : NodeRequest Symbol Guard)
    (left : input.left.free = []) (right : input.right.free = []) :
    ∃ key, SourceRecursiveIntersectionMemo.requestKey width input.domain input.left input.right = some key := by
  have keyable : ∀ value : Value Symbol Guard, value.free = [] →
      ∃ tagged, IntersectionFlatMemoKey.input value.referenceOf = some tagged := by
    intro value closed
    cases value <;> simp_all [Value.free,Value.referenceOf,IntersectionFlatMemoKey.input]
  obtain ⟨first,firstInput⟩ := keyable input.left left
  obtain ⟨second,secondInput⟩ := keyable input.right right
  exact ⟨_,IntersectionFlatMemoKeyDomain.sourceKey_complete width input.domain _ _ first second firstInput secondInput⟩

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- An actual request retains its direct body or its complete returned cell and earlier writer. -/
def Origin (input : NodeRequest Symbol Guard) (before : Checked width)
    (result : Value Symbol Guard) (after : Checked width) : Prop :=
  (SourceRecursiveIntersectionMemo.requestKey width input.domain input.left input.right = none ∧
    ∃ fuel, Trace fuel (.code (compileNode input)) before (.code (.pure result)) after) ∨
  ∃ handle, after.native.nodes.cells handle = some ⟨input,.returned result⟩ ∧
    SourceCurrentNativeWriterReadyRetention.Written (width := width) handle input result after.native

/-- Closed request operands exclude the unresolved direct case. -/
theorem Origin.returned {input : NodeRequest Symbol Guard} {before after : Checked width}
    {result : Value Symbol Guard} (origin : Origin input before result after)
    (left : input.left.free = []) (right : input.right.free = []) :
    ∃ handle, after.native.nodes.cells handle = some ⟨input,.returned result⟩ ∧
      SourceCurrentNativeWriterReadyRetention.Written (width := width) handle input result after.native := by
  rcases origin with ⟨unresolved,_⟩ | returned
  · obtain ⟨key,present⟩ := closed_key input left right
    rw [present] at unresolved
    cases unresolved
  · exact returned

private theorem stopped {before after : Checked width} (input : NodeRequest Symbol Guard)
    (fuel : Nat) (result : Value Symbol Guard) (good : Good before)
    (actual : Trace fuel (.code (requestNode input.domain input.left input.right)) before (.code (.pure result)) after) :
    (SourceRecursiveIntersectionMemo.requestKey width input.domain input.left input.right = none ∧
      ∃ count, Trace count (.code (compileNode input)) before (.code (.pure result)) after) ∨
    ∃ handle, after.native.nodes.cells handle = some ⟨input,.returned result⟩ := by
  cases actual with
  | cons _ _ resume reached _ _ rest inputs one tail =>
    cases key : SourceRecursiveIntersectionMemo.requestKey width input.domain input.left input.right with
    | none =>
      have selected := lookupNode_bypass width input before.native key
      obtain ⟨rfl,rfl⟩ := Outcome.yielded.inj (by
        simpa only [step,SourceRecursiveIntersectionNative.step,requestNode,selected,lift] using one)
      exact Or.inl ⟨rfl,rest,by simpa only [code_bind_pure] using tail⟩
    | some requested =>
      have safe := inputs.2 requested key
      cases selected : lookupNode width input before.native with
      | mk selection chosen =>
        cases selection with
        | direct original =>
          simp only [lookupNode,key] at selected
          cases selected
        | memoized handle =>
          cases demanded : demandNode handle chosen with
          | mk observation running =>
            cases observation with
            | absent | busy =>
              simp only [step,SourceRecursiveIntersectionNative.step,requestNode,selected,demanded,lift] at one
              cases one
            | ready value =>
              have receipt := SourceCurrentAllocatedNativePhysicalCache.node_ready input before.native chosen running handle value
                good.native inputs.1 safe selected demanded
              obtain ⟨rfl,rfl⟩ := Outcome.yielded.inj (by
                simpa only [step,SourceRecursiveIntersectionNative.step,requestNode,selected,demanded,lift] using one)
              obtain ⟨rfl,rfl,rfl⟩ := pure_trace rest value result _ after tail.steps
              exact Or.inr ⟨handle,by simpa only [receipt.2.1] using receipt.1⟩
            | evaluate original =>
              have same := SourceCurrentAllocatedNativePhysicalCache.node_started input original before.native chosen running handle
                good.native inputs.1 safe selected demanded
              subst original
              obtain ⟨rfl,rfl⟩ := Outcome.yielded.inj (by
                simpa only [step,SourceRecursiveIntersectionNative.step,requestNode,selected,demanded,lift] using one)
              obtain ⟨inner,outer,value,current,_,bodyTrace,frameTrace⟩ := bind_inverse rest
                (.code (compileNode input)) (fun value => .finishNode handle value (.pure value))
                ⟨running,before.operations⟩ after result tail
              have chosenGood := SourceCurrentAllocatedNativePhysicalCache.lookupNode_valid before.native good.native input inputs.1 safe
              simp only [selected] at chosenGood
              have runningGood := SourceCurrentAllocatedNativePhysicalCache.demandNode_valid chosen chosenGood handle
              simp only [demanded] at runningGood
              have owner := (SourceRecursiveIntersectionNative.demandNode_evaluate handle chosen running input demanded).2
              have retained := SourceEqualityNativeDemandProtectedPrefix.node_body_owner inner handle input
                ⟨running,before.operations⟩ current value runningGood.shape owner bodyTrace.steps
              cases frameTrace with
              | cons _ _ next final _ _ count _ frameStep remaining =>
                obtain ⟨rfl,rfl⟩ := Outcome.yielded.inj frameStep
                obtain ⟨rfl,rfl,rfl⟩ := pure_trace count value result _ after remaining.steps
                exact Or.inr ⟨handle,retained.2⟩

/-- Initial native history and actual execution derive the exact completed request lineage. -/
theorem request {before after : Checked width} (input : NodeRequest Symbol Guard)
    (fuel : Nat) (result : Value Symbol Guard) (good : Good before) (history : History before)
    (actual : Trace fuel (.code (requestNode input.domain input.left input.right)) before (.code (.pure result)) after) :
    History after ∧ Good after ∧ Grows before.native.machine.heap after.native.machine.heap ∧
      Origin input before result after := by
  have reached := history.query input fuel result good actual
  have checked := effects actual good (by intro value; trivial)
  refine ⟨reached,checked.1,checked.2.2.1.growth,?_⟩
  rcases stopped input fuel result good actual with direct | ⟨handle,present⟩
  · exact Or.inl direct
  · exact Or.inr ⟨handle,present,SourceCurrentNativeWriterReadyRetention.writers reached handle input result present⟩

/-- Actual leaf reads retain historical targets on hits and derive their own native request writer. -/
theorem leaf {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {record values path input before result after memos final}
    {actual : SourceCurrentAllocatedSharedTargetLeaf.Leaf (width := width) record values path input before result after}
    (reads : SourceCurrentAllocatedSharedTargetLeaf.Reads formulas solver actual memos final)
    (history : History before.checked) :
    ∃ target : Value Symbol Guard, ∃ middle : Shared width, ∃ forceInventory next : Inventory, ∃ base : Heap,
      SourceCurrentAllocatedSharedTargetForce.Receipt formulas solver forceInventory record values base path
        before target middle memos final ∧
      SourceCurrentAllocatedTargetQuery.Receipt formulas solver next target input middle.checked result after.checked final ∧
      after = SourceCurrentAllocatedSharedTargetState.advance middle after.checked ∧
      SourceCurrentAllocatedSharedTargetState.SlotReceipt width formulas solver record values
        middle.checked.native.machine.heap middle.memo path target ∧
      History middle.checked ∧ History after.checked ∧ Good middle.checked ∧ Good after.checked ∧
      Grows before.checked.native.machine.heap middle.checked.native.machine.heap ∧
      Grows middle.checked.native.machine.heap after.checked.native.machine.heap ∧
      Origin ⟨IntersectionEmptyDomain.emptyDomain,target,input⟩ middle.checked result after.checked := by
  cases reads with
  | apply first query =>
    have middleHistory := SourceCurrentParentNativeHistory.force first history
    have targetOrigin := first.ready.receipts _ _ first.present
    cases query.actual with
    | run trace =>
      have current := request ⟨IntersectionEmptyDomain.emptyDomain,_,_⟩ _ _ first.ready.checked.good middleHistory trace
      exact ⟨_,_,_,_,_,first,query,rfl,targetOrigin,middleHistory,current.1,first.ready.checked.good,
        current.2.1,first.effects.keeps.growth,current.2.2.1,current.2.2.2⟩

end MicroCFTA.SourceCurrentSharedLeafNativeLineage
