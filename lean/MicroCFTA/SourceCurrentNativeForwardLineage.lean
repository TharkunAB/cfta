import MicroCFTA.SourceCurrentNativeWriterReadyRetention

/-!
# Exact native forwarding and self lineage

Swap and reset forward the actual captured request. A completed forwarded
call either keeps its unresolved direct body or returns a captured cell.
Actual ready-cell retention transfers that cell into the final reader.
The final history supplies its protected writer without internal history.
The self branch returns the literal left input at the same checked state.
-/
namespace MicroCFTA.SourceCurrentNativeForwardLineage
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativeSemanticTraceReadback (bind_inverse)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentNativeEdgeWriterGrowth (History)
open SourceEqualityNativeDemandMemo (Retained)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A literal forwarded call retains its direct body or its exact returned cell and writer at the final reader. -/
def Forwarded (reader : Checked width) (request : NodeRequest Symbol Guard)
    (before after : Checked width) (result : Value Symbol Guard) : Prop :=
  (∃ fuel, Trace fuel (.code (requestNode request.domain request.left request.right))
    before (.code (.pure result)) after) ∧
  ((SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = none ∧
      ∃ fuel, Trace fuel (.code (compileNode request)) before (.code (.pure result)) after) ∨
    ∃ handle, reader.native.nodes.cells handle = some ⟨request,.returned result⟩ ∧
      SourceCurrentNativeWriterReadyRetention.Written (width := width) handle request result reader.native)

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

private theorem forwarded {before after reader : Checked width} (history : History reader)
    (request : NodeRequest Symbol Guard) (fuel : Nat) (result : Value Symbol Guard) (good : Good before)
    (actual : Trace fuel (.code (requestNode request.domain request.left request.right)) before (.code (.pure result)) after)
    (retained : Retained after.native reader.native) : Forwarded reader request before after result := by
  refine ⟨⟨fuel,actual⟩,?_⟩
  rcases stopped request fuel result good actual with direct | ⟨handle,stored⟩
  · exact Or.inl direct
  · have present := retained.nodes handle request result stored
    exact Or.inr ⟨handle,present,SourceCurrentNativeWriterReadyRetention.writers history handle request result present⟩

/-- An actual swap body retains the exact reversed request and its final-reader provenance. -/
theorem swap {before after reader : Checked width} (history : History reader)
    (request : NodeRequest Symbol Guard) (fuel : Nat) (result : Value Symbol Guard) (good : Good before)
    (actual : Trace fuel (.code (compileNode request)) before (.code (.pure result)) after)
    (retained : Retained after.native reader.native)
    (selected : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .swap) :
    Forwarded reader ⟨request.domain,request.right,request.left⟩ before after result := by
  have compiled : compileNode request = requestNode request.domain request.right request.left := by
    unfold compileNode
    simp only [selected]
  rw [compiled] at actual
  exact forwarded history _ fuel result good actual retained

/-- An actual reset body retains the empty-domain request with the same ordered operands. -/
theorem reset {before after reader : Checked width} (history : History reader)
    (request : NodeRequest Symbol Guard) (fuel : Nat) (result : Value Symbol Guard) (good : Good before)
    (actual : Trace fuel (.code (compileNode request)) before (.code (.pure result)) after)
    (retained : Retained after.native reader.native)
    (selected : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .reset) :
    Forwarded reader ⟨IntersectionEmptyDomain.emptyDomain,request.left,request.right⟩ before after result := by
  have compiled : compileNode request = requestNode IntersectionEmptyDomain.emptyDomain request.left request.right := by
    unfold compileNode
    simp only [selected]
  rw [compiled] at actual
  exact forwarded history _ fuel result good actual retained

/-- A captured self body returns its literal left operand with no checked transition or state change. -/
theorem self {before after : Checked width} (request : NodeRequest Symbol Guard)
    (fuel : Nat) (result : Value Symbol Guard)
    (actual : Trace fuel (.code (compileNode request)) before (.code (.pure result)) after)
    (selected : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .self) :
    fuel = 0 ∧ result = request.left ∧ after = before := by
  have compiled : compileNode request = .pure request.left := by
    unfold compileNode
    simp only [selected]
  rw [compiled] at actual
  have stopped := pure_trace fuel request.left result before after actual.steps
  exact ⟨stopped.1,stopped.2.1.symm,stopped.2.2.symm⟩

/-- A current returned cell derives its captured protected writer and actual swap, reset, or self lineage. -/
theorem writer {reader : Checked width} (history : History reader) (handle : Nat)
    (request : NodeRequest Symbol Guard) (result : Value Symbol Guard)
    (returned : reader.native.nodes.cells handle = some ⟨request,.returned result⟩)
    (selected : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .swap ∨
      SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .reset ∨
      SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .self) :
    ∃ (before after : Checked width) (fuel : Nat),
      Good before ∧ NodeReady before.native.machine request ∧
      before.native.nodes.cells handle = some ⟨request,.evaluating⟩ ∧
      Trace fuel (.code (compileNode request)) before (.code (.pure result)) after ∧
      after.native.nodes.cells handle = some ⟨request,.evaluating⟩ ∧
      Trace 1 (.code (.finishNode handle result (.pure result))) after (.code (.pure result))
        {after with native := finishNode handle result after.native} ∧
      Grows before.native.machine.heap reader.native.machine.heap ∧
      Grows after.native.machine.heap reader.native.machine.heap ∧ Retained after.native reader.native ∧
      ((SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .swap ∧
          Forwarded reader ⟨request.domain,request.right,request.left⟩ before after result) ∨
        (SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .reset ∧
          Forwarded reader ⟨IntersectionEmptyDomain.emptyDomain,request.left,request.right⟩ before after result) ∨
        (SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .self ∧
          fuel = 0 ∧ result = request.left ∧ after = before)) := by
  obtain ⟨before,after,fuel,good,ready,owner,body,ownerKept,finish,first,last,retained⟩ :=
    SourceCurrentNativeWriterReadyRetention.writers history handle request result returned
  refine ⟨before,after,fuel,good,ready,owner,body,ownerKept,finish,first,last,retained,?_⟩
  rcases selected with swapped | reset | same
  · exact Or.inl ⟨swapped,swap history request fuel result good body retained swapped⟩
  · exact Or.inr (Or.inl ⟨reset,SourceCurrentNativeForwardLineage.reset history request fuel result good body retained reset⟩)
  · exact Or.inr (Or.inr ⟨same,self request fuel result body same⟩)

end MicroCFTA.SourceCurrentNativeForwardLineage
