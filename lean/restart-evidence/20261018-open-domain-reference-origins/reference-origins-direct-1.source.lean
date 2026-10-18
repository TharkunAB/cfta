import MicroCFTA.SourceCurrentNativeForwardLineage

/-!
# Actual native reference resolution origins

A successful reference body reads one exact binding at its unchanged
checked entry. Its recursive request retains the original operand order.
Final reader history supplies earlier writers for returned child cells.
Direct placeholder requests retain their actual compiler trace instead.
-/
namespace MicroCFTA.SourceCurrentNativeReferenceOrigins
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativeSemanticTraceReadback (bind_inverse)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentNativeEdgeWriterGrowth (History)
open SourceEqualityNativeDemandMemo (Retained)
open SourceCurrentNativeForwardLineage (Forwarded)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem failed_body {before after : Checked width} (fuel : Nat)
    (failure : SourceRecursiveIntersectionKernel.Failure) (result : Value Symbol Guard)
    (actual : Trace fuel (.code (.fail failure)) before (.code (.pure result)) after) : False := by
  cases actual with
  | cons _ _ _ _ _ _ _ _ one _ => cases one

/-- A successful reference read retains its exact binding and ordered child call at the same entry. -/
theorem reference {before after : Checked width}
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (name : Nat)
    (other : Value Symbol Guard) (left : Bool) (fuel : Nat) (result : Value Symbol Guard)
    (actual : Trace fuel (.code (compileReference domain name other left)) before (.code (.pure result)) after) :
    ∃ (bound : Value Symbol Guard) (childFuel : Nat),
      fuel = childFuel + 1 ∧ name ∈ SourceRecursiveIntersectionDomain.names domain.key ∧
      SourcePreparedSharedRows.read before.native.machine.heap name = some bound ∧
      Trace childFuel (.code (if left then requestNode domain bound other else requestNode domain other bound))
        before (.code (.pure result)) after := by
  by_cases member : name ∈ SourceRecursiveIntersectionDomain.names domain.key
  · simp only [compileReference,member,ite_true] at actual
    cases actual with
    | cons _ _ next current _ _ count _ one tail =>
        cases found : SourcePreparedSharedRows.read before.native.machine.heap name with
        | none =>
            obtain ⟨rfl,rfl⟩ := Outcome.yielded.inj (by
              simpa only [step,SourceRecursiveIntersectionNative.step,found,lift] using one)
            exact (failed_body count _ result tail).elim
        | some bound =>
            obtain ⟨rfl,rfl⟩ := Outcome.yielded.inj (by
              simpa only [step,SourceRecursiveIntersectionNative.step,found,lift] using one)
            exact ⟨bound,count,rfl,member,found,tail⟩
  · exact (failed_body fuel _ result (by
      simpa only [compileReference,member,ite_false] using actual)).elim

/-- The actual left-reference branch derives the interned name and its exact resolved child trace. -/
theorem left {before after : Checked width} (request : NodeRequest Symbol Guard)
    (fuel : Nat) (result : Value Symbol Guard)
    (actual : Trace fuel (.code (compileNode request)) before (.code (.pure result)) after)
    (selected : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .leftReference) :
    ∃ (name : Nat) (bound : Value Symbol Guard) (childFuel : Nat),
      request.left = .reference (.interned name) ∧ fuel = childFuel + 1 ∧
      name ∈ SourceRecursiveIntersectionDomain.names request.domain.key ∧
      SourcePreparedSharedRows.read before.native.machine.heap name = some bound ∧
      Trace childFuel (.code (requestNode request.domain bound request.right)) before (.code (.pure result)) after := by
  have shape : ∃ name, request.left = .reference (.interned name) := by
    cases found : request.left with
    | reference ref =>
        cases ref with
        | interned name => exact ⟨name,rfl⟩
        | uninterned | depth | intersection | state =>
            have impossible := actual
            unfold compileNode at impossible
            dsimp only at impossible
            rw [selected,found] at impossible
            exact (failed_body fuel _ result impossible).elim
    | empty | node | union | mu =>
        have impossible := actual
        unfold compileNode at impossible
        dsimp only at impossible
        rw [selected,found] at impossible
        exact (failed_body fuel _ result impossible).elim
  obtain ⟨name,shape⟩ := shape
  have called : Trace fuel (.code (compileReference request.domain name request.right true))
      before (.code (.pure result)) after := by
    simpa only [compileNode,selected,shape] using actual
  obtain ⟨bound,count,total,member,found,tail⟩ := reference request.domain name request.right true fuel result called
  exact ⟨name,bound,count,shape,total,member,found,tail⟩

/-- The actual right-reference branch derives the binding without changing the left operand. -/
theorem right {before after : Checked width} (request : NodeRequest Symbol Guard)
    (fuel : Nat) (result : Value Symbol Guard)
    (actual : Trace fuel (.code (compileNode request)) before (.code (.pure result)) after)
    (selected : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .rightReference) :
    ∃ (name : Nat) (bound : Value Symbol Guard) (childFuel : Nat),
      request.right = .reference (.interned name) ∧ fuel = childFuel + 1 ∧
      name ∈ SourceRecursiveIntersectionDomain.names request.domain.key ∧
      SourcePreparedSharedRows.read before.native.machine.heap name = some bound ∧
      Trace childFuel (.code (requestNode request.domain request.left bound)) before (.code (.pure result)) after := by
  have shape : ∃ name, request.right = .reference (.interned name) := by
    cases found : request.right with
    | reference ref =>
        cases ref with
        | interned name => exact ⟨name,rfl⟩
        | uninterned | depth | intersection | state =>
            have impossible := actual
            unfold compileNode at impossible
            dsimp only at impossible
            rw [selected,found] at impossible
            exact (failed_body fuel _ result impossible).elim
    | empty | node | union | mu =>
        have impossible := actual
        unfold compileNode at impossible
        dsimp only at impossible
        rw [selected,found] at impossible
        exact (failed_body fuel _ result impossible).elim
  obtain ⟨name,shape⟩ := shape
  have called : Trace fuel (.code (compileReference request.domain name request.left false))
      before (.code (.pure result)) after := by
    simpa only [compileNode,selected,shape] using actual
  obtain ⟨bound,count,total,member,found,tail⟩ := reference request.domain name request.left false fuel result called
  exact ⟨name,bound,count,shape,total,member,found,tail⟩

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

/-- A completed request retains its direct trace or exact child writer at the final reader. -/
theorem forwarded {before after reader : Checked width} (history : History reader)
    (request : NodeRequest Symbol Guard) (fuel : Nat) (result : Value Symbol Guard) (good : Good before)
    (actual : Trace fuel (.code (requestNode request.domain request.left request.right)) before (.code (.pure result)) after)
    (retained : Retained after.native reader.native) : Forwarded reader request before after result := by
  refine ⟨⟨fuel,actual⟩,?_⟩
  rcases stopped request fuel result good actual with direct | ⟨handle,stored⟩
  · exact Or.inl direct
  · have present := retained.nodes handle request result stored
    exact Or.inr ⟨handle,present,SourceCurrentNativeWriterReadyRetention.writers history handle request result present⟩

end MicroCFTA.SourceCurrentNativeReferenceOrigins
