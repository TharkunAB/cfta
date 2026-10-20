import MicroCFTA.SourceCurrentNativeOpenQueryForwarding
import MicroCFTA.SourceCurrentNativeRowKeyable

/-!
# Actual forwarding writers at an active reader

A returned-writer map replaces completed native history at the reader.
The supplied forwarded call keeps its exact request and selected writer.
Actual swap and reset bodies reach a terminal writer at that same reader.
The normalization measure covers only swap and reset.
-/
namespace MicroCFTA.SourceCurrentNativeActiveQueryForwarding
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativeSemanticTraceReadback (bind_inverse)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceEqualityNativeDemandMemo (Retained)
open SourceCurrentNativeForwardLineage (Forwarded)
open SourceCurrentNativeQueryRowOrigins (Route)
open SourceRecursiveIntersectionControl (decision reset greater)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat}

private theorem payload_not_forward (left right : Value Symbol Guard) :
    SourceRecursiveIntersectionControl.payload left right ≠ .swap ∧
    SourceRecursiveIntersectionControl.payload left right ≠ .reset := by
  cases left <;> cases right <;> simp [SourceRecursiveIntersectionControl.payload]

private theorem swap_tests (request : NodeRequest Symbol Guard)
    (selected : decision request.domain.key request.left request.right = .swap) :
    reset request.domain.key request.left request.right = false ∧ greater request.left request.right = true := by
  unfold decision at selected
  split at selected
  · cases selected
  · split at selected
    · cases selected
    · rename_i restart
      split at selected
      · cases selected
      · split at selected
        · exact ⟨Bool.eq_false_iff.mpr restart,by assumption⟩
        · cases first : SourceRecursiveIntersectionControl.identity request.left <;>
            cases second : SourceRecursiveIntersectionControl.identity request.right <;>
            simp only [first,second] at selected
          all_goals try cases selected
          split at selected
          · cases selected
          · exact False.elim ((payload_not_forward request.left request.right).1 selected)

private theorem reset_test (request : NodeRequest Symbol Guard)
    (selected : decision request.domain.key request.left request.right = .reset) :
    reset request.domain.key request.left request.right = true := by
  unfold decision at selected
  split at selected
  · cases selected
  · split at selected
    · assumption
    · split at selected
      · cases selected
      · split at selected
        · cases selected
        · cases first : SourceRecursiveIntersectionControl.identity request.left <;>
            cases second : SourceRecursiveIntersectionControl.identity request.right <;>
            simp only [first,second] at selected
          all_goals try cases selected
          split at selected
          · cases selected
          · exact False.elim ((payload_not_forward request.left request.right).2 selected)

private def measure (request : NodeRequest Symbol Guard) : Nat :=
  if reset request.domain.key request.left request.right then 2 else if greater request.left request.right then 1 else 0

private theorem swap_decreases (request : NodeRequest Symbol Guard)
    (left : ∃ first, IntersectionFlatMemoKey.input request.left.referenceOf = some first)
    (right : ∃ second, IntersectionFlatMemoKey.input request.right.referenceOf = some second)
    (selected : decision request.domain.key request.left request.right = .swap) :
    measure ⟨request.domain,request.right,request.left⟩ < measure request := by
  obtain ⟨restart,ordered⟩ := swap_tests request selected
  obtain ⟨first,firstInput⟩ := left
  obtain ⟨second,secondInput⟩ := right
  have reversed := SourceRecursiveIntersectionSchedule.swap_once request.left request.right first second firstInput secondInput ordered
  have same : reset request.domain.key request.right request.left = false := by
    simpa only [reset,Bool.and_assoc,Bool.and_left_comm] using restart
  simp only [measure,restart,ordered,same,reversed,Bool.false_eq_true,ite_false,ite_true]
  decide

private theorem reset_decreases (request : NodeRequest Symbol Guard)
    (selected : decision request.domain.key request.left request.right = .reset) :
    measure ⟨IntersectionEmptyDomain.emptyDomain,request.left,request.right⟩ < measure request := by
  have restart := reset_test request selected
  simp only [measure,restart,ite_true]
  simp only [reset,IntersectionEmptyDomain.emptyDomain,IntersectionEmptyDomain.emptyKey,
    List.isEmpty_nil,Bool.not_true,Bool.and_false,Bool.false_eq_true,ite_false]
  split <;> decide

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

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

/-- A completed call derives its direct body or retained returned writer from the same reader map. -/
theorem forwarded {before after reader : Checked width}
    (writers : ∀ (handle : Nat) (request : NodeRequest Symbol Guard) (result : Value Symbol Guard),
      reader.native.nodes.cells handle = some ⟨request,.returned result⟩ →
        SourceCurrentNativeWriterReadyRetention.Written handle request result reader.native)
    (request : NodeRequest Symbol Guard) (fuel : Nat) (result : Value Symbol Guard) (good : Good before)
    (actual : Trace fuel (.code (requestNode request.domain request.left request.right)) before (.code (.pure result)) after)
    (retained : Retained after.native reader.native) : Forwarded reader request before after result := by
  refine ⟨⟨fuel,actual⟩,?_⟩
  rcases stopped request fuel result good actual with direct | ⟨handle,stored⟩
  · exact Or.inl direct
  · have present := retained.nodes handle request result stored
    exact Or.inr ⟨handle,present,writers handle request result present⟩

private theorem forwarded_returned {before after reader : Checked width}
    (request : NodeRequest Symbol Guard) (result : Value Symbol Guard)
    (left : ∃ first, IntersectionFlatMemoKey.input request.left.referenceOf = some first)
    (right : ∃ second, IntersectionFlatMemoKey.input request.right.referenceOf = some second)
    (forwarded : SourceCurrentNativeForwardLineage.Forwarded reader request before after result) :
    ∃ handle, reader.native.nodes.cells handle = some ⟨request,.returned result⟩ ∧
      SourceCurrentNativeWriterReadyRetention.Written handle request result reader.native := by
  rcases forwarded.2 with ⟨unresolved,_⟩ | ⟨handle,present,written⟩
  · obtain ⟨first,firstInput⟩ := left
    obtain ⟨second,secondInput⟩ := right
    have key := IntersectionFlatMemoKeyDomain.sourceKey_complete width request.domain _ _ first second firstInput secondInput
    change IntersectionFlatMemoKeyDomain.sourceKey width request.domain request.left.referenceOf request.right.referenceOf = none at unresolved
    rw [key] at unresolved
    cases unresolved
  · exact ⟨handle,present,written⟩

private theorem normalize_writer {reader : Checked width}
    (writers : ∀ (handle : Nat) (request : NodeRequest Symbol Guard) (result : Value Symbol Guard),
      reader.native.nodes.cells handle = some ⟨request,.returned result⟩ →
        SourceCurrentNativeWriterReadyRetention.Written handle request result reader.native)
    (request : NodeRequest Symbol Guard) (result : Value Symbol Guard)
    (left : ∃ first, IntersectionFlatMemoKey.input request.left.referenceOf = some first)
    (right : ∃ second, IntersectionFlatMemoKey.input request.right.referenceOf = some second)
    (returned : ∃ handle,reader.native.nodes.cells handle = some ⟨request,.returned result⟩ ∧
      SourceCurrentNativeWriterReadyRetention.Written handle request result reader.native) :
    ∃ terminal handle, Route reader result request terminal ∧
      reader.native.nodes.cells handle = some ⟨terminal,.returned result⟩ ∧
      SourceCurrentNativeWriterReadyRetention.Written (width := width) handle terminal result reader.native ∧
      decision terminal.domain.key terminal.left terminal.right ≠ .swap ∧
      decision terminal.domain.key terminal.left terminal.right ≠ .reset ∧
      (∃ first, IntersectionFlatMemoKey.input terminal.left.referenceOf = some first) ∧
      (∃ second, IntersectionFlatMemoKey.input terminal.right.referenceOf = some second) := by
  generalize boundEq : measure request = bound
  induction bound using Nat.strongRecOn generalizing request with
  | ind bound ih =>
    obtain ⟨handle,present,writer⟩ := returned
    by_cases swap : decision request.domain.key request.left request.right = .swap
    · obtain ⟨before,after,fuel,good,_,_,actual,_,_,_,_,retained⟩ := writer
      have compiled : compileNode request = requestNode request.domain request.right request.left := by
        unfold compileNode
        simp only [swap]
      have forwarded := forwarded writers ⟨request.domain,request.right,request.left⟩ fuel result good
        (compiled ▸ actual) retained
      obtain ⟨next,stored,nextWriter⟩ := forwarded_returned _ result right left forwarded
      obtain ⟨terminal,final,route,cell,written,notSwap,notReset,firstCodec,secondCodec⟩ := ih _
        (by rw [← boundEq]; exact swap_decreases request left right swap)
        ⟨request.domain,request.right,request.left⟩ right left ⟨next,stored,nextWriter⟩ rfl
      exact ⟨terminal,final,.step ⟨before,after,fuel,good,actual,retained,.inl ⟨swap,rfl⟩,forwarded⟩ route,
        cell,written,notSwap,notReset,firstCodec,secondCodec⟩
    · by_cases restart : decision request.domain.key request.left request.right = .reset
      · obtain ⟨before,after,fuel,good,_,_,actual,_,_,_,_,retained⟩ := writer
        have compiled : compileNode request = requestNode IntersectionEmptyDomain.emptyDomain request.left request.right := by
          unfold compileNode
          simp only [restart]
        have forwarded := forwarded writers ⟨IntersectionEmptyDomain.emptyDomain,request.left,request.right⟩ fuel result good
          (compiled ▸ actual) retained
        obtain ⟨next,stored,nextWriter⟩ := forwarded_returned
          ⟨IntersectionEmptyDomain.emptyDomain,request.left,request.right⟩ result left right forwarded
        obtain ⟨terminal,final,route,cell,written,notSwap,notReset,firstCodec,secondCodec⟩ := ih _
          (by rw [← boundEq]; exact reset_decreases request restart)
          ⟨IntersectionEmptyDomain.emptyDomain,request.left,request.right⟩ left right ⟨next,stored,nextWriter⟩ rfl
        exact ⟨terminal,final,.step ⟨before,after,fuel,good,actual,retained,.inr ⟨restart,rfl⟩,forwarded⟩ route,
          cell,written,notSwap,notReset,firstCodec,secondCodec⟩
      · exact ⟨request,handle,.refl request,present,writer,swap,restart,left,right⟩

/-- A nonempty actual forwarded result reaches a terminal historical writer at the same active reader. -/
theorem normalize {reader before after : Checked width}
    (writers : ∀ (handle : Nat) (request : NodeRequest Symbol Guard) (result : Value Symbol Guard),
      reader.native.nodes.cells handle = some ⟨request,.returned result⟩ →
        SourceCurrentNativeWriterReadyRetention.Written handle request result reader.native)
    (request : NodeRequest Symbol Guard) (result : Value Symbol Guard)
    (actual : Forwarded reader request before after result)
    (nonempty : result ≠ .empty) :
    ∃ terminal handle, Route reader result request terminal ∧
      reader.native.nodes.cells handle = some ⟨terminal,.returned result⟩ ∧
      SourceCurrentNativeWriterReadyRetention.Written handle terminal result reader.native ∧
      decision terminal.domain.key terminal.left terminal.right ≠ .swap ∧
      decision terminal.domain.key terminal.left terminal.right ≠ .reset ∧
      (∃ first, IntersectionFlatMemoKey.input terminal.left.referenceOf = some first) ∧
      (∃ second, IntersectionFlatMemoKey.input terminal.right.referenceOf = some second) := by
  obtain ⟨fuel,called⟩ := actual.1
  have keyed : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right ≠ none := by
    intro missing
    exact nonempty (SourceCurrentNativeRowKeyable.unkeyed_empty request fuel result missing called)
  have codecs : (∃ first, IntersectionFlatMemoKey.input request.left.referenceOf = some first) ∧
      (∃ second, IntersectionFlatMemoKey.input request.right.referenceOf = some second) := by
    cases first : IntersectionFlatMemoKey.input request.left.referenceOf with
    | none =>
      exact (keyed (by simp [SourceRecursiveIntersectionMemo.requestKey,
        IntersectionFlatMemoKeyDomain.sourceKey,IntersectionFlatMemoKey.key,first])).elim
    | some firstValue =>
      cases second : IntersectionFlatMemoKey.input request.right.referenceOf with
      | none =>
        exact (keyed (by simp [SourceRecursiveIntersectionMemo.requestKey,
          IntersectionFlatMemoKeyDomain.sourceKey,IntersectionFlatMemoKey.key,second])).elim
      | some secondValue => exact ⟨⟨firstValue,rfl⟩,⟨secondValue,rfl⟩⟩
  obtain ⟨handle,present,written⟩ := forwarded_returned request result codecs.1 codecs.2 actual
  exact normalize_writer writers request result codecs.1 codecs.2 ⟨handle,present,written⟩

end MicroCFTA.SourceCurrentNativeActiveQueryForwarding
