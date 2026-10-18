import MicroCFTA.SourceCurrentNativeReferenceOrigins
import MicroCFTA.SourceCurrentNativeMuWriterOrigins

/-!
# Actual open body requests at native Mu writers

The captured entry derives the full checked state after domain allocation.
The actual open body call retains its direct trace or earlier returned
writer at the final reader. No history at the active body entry is assumed.
-/
namespace MicroCFTA.SourceCurrentNativeMuBodyOrigins
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativeSemanticTraceReadback (current_inputs effects)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentNativeEdgeWriterGrowth (History)
open SourceEqualityNativeDemandMemo (Retained)
open SourceRecursiveIntersectionControl (decision identity pair)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- The actual entered body retains both checked states and final-reader request provenance. -/
def Body (reader : Checked width) (fuel : Nat) (request : NodeRequest Symbol Guard)
    (before : Checked width) (result : Value Symbol Guard) (after : Checked width) : Prop :=
  ∃ first second childFuel bodyValue middle heap,
    let entered := SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains request.domain.key
      request.left request.right first second
    let entry := {before with native := advance before.native {before.native.machine with domains := entered.2}}
    identity request.left = some first ∧ identity request.right = some second ∧
    fuel = childFuel + 2 ∧ Good entry ∧
    Trace childFuel (.code (requestNode entered.1 (body request.left) (body request.right)))
      entry (.code (.pure bodyValue)) middle ∧ Good middle ∧
    SourceCurrentNativeForwardLineage.Forwarded reader
      ⟨entered.1,body request.left,body request.right⟩ entry middle bodyValue ∧
    Available middle.native.machine.heap bodyValue ∧
    SourceRecursiveIntersectionMaybeMu.maybeMu (pair first second) bodyValue middle.native.machine.heap =
      .done result heap ∧
    after = {middle with native := advance middle.native {middle.native.machine with heap := heap}}

/-- A completed Mu body derives its checked open child entry and exact request origin. -/
theorem trace {before after reader : Checked width} (history : History reader)
    (request : NodeRequest Symbol Guard) (fuel : Nat) (result : Value Symbol Guard)
    (good : Good before)
    (actual : Trace fuel (.code (compileMu request.domain request.left request.right)) before (.code (.pure result)) after)
    (retained : Retained after.native reader.native) : Body reader fuel request before result after := by
  obtain ⟨first,second,childFuel,bodyValue,middle,heap,leftId,rightId,count,child,available,binder,final,_⟩ :=
    SourceCurrentNativeMuWriterOrigins.trace request fuel before after result actual
  have one := SourceCurrentAllocatedNativeMuSource.enter_prefix request before first second leftId rightId
  have reached := SourceCurrentAllocatedNativePhysicalCompletion.step_invariants
    (.code (compileMu request.domain request.left request.right)) before good (current_inputs actual)
    (SourceCurrentAllocatedNativeCodeFields.compileMu_fields before.operations request.domain request.left request.right)
  rw [one] at reached
  have middleGood := (effects child reached.1 (by intro value; trivial)).1
  have middleRetained : Retained middle.native reader.native := by
    have next := SourceEqualityNativeDemandMemo.advance_retained middle.native {middle.native.machine with heap := heap}
    rw [final] at retained
    exact next.trans retained
  have origin := SourceCurrentNativeReferenceOrigins.forwarded history
    ⟨_,body request.left,body request.right⟩ childFuel bodyValue reached.1 child middleRetained
  exact ⟨first,second,childFuel,bodyValue,middle,heap,leftId,rightId,count,reached.1,
    child,middleGood,origin,available,binder,final⟩

/-- A returned Mu cell retains its captured owner and the checked open body provenance. -/
theorem returned {reader : Checked width} (history : History reader)
    (request : NodeRequest Symbol Guard) (result : Value Symbol Guard) (handle : Nat)
    (present : reader.native.nodes.cells handle = some ⟨request,.returned result⟩)
    (selected : decision request.domain.key request.left request.right = .bothMu ∨
      decision request.domain.key request.left request.right = .leftMu ∨
      decision request.domain.key request.left request.right = .rightMu) :
    ∃ before after fuel, Good before ∧ NodeReady before.native.machine request ∧
      before.native.nodes.cells handle = some ⟨request,.evaluating⟩ ∧
      Trace fuel (.code (compileNode request)) before (.code (.pure result)) after ∧
      Body reader fuel request before result after ∧
      after.native.nodes.cells handle = some ⟨request,.evaluating⟩ ∧
      Trace 1 (.code (.finishNode handle result (.pure result))) after (.code (.pure result))
        {after with native := finishNode handle result after.native} ∧
      Grows before.native.machine.heap reader.native.machine.heap ∧
      Grows after.native.machine.heap reader.native.machine.heap ∧ Retained after.native reader.native := by
  obtain ⟨before,after,fuel,good,ready,owner,actual,kept,finish,first,last,retained⟩ :=
    SourceCurrentNativeWriterReadyRetention.writers history handle request result present
  have compiled : compileNode request = compileMu request.domain request.left request.right := by
    rcases selected with selected | selected | selected <;> simp only [compileNode,selected]
  exact ⟨before,after,fuel,good,ready,owner,actual,
    trace history request fuel result good (compiled ▸ actual) retained,kept,finish,first,last,retained⟩

private theorem identity_keyable (value : Value Symbol Guard) (name : Nat) (named : identity value = some name) :
    ∃ input, IntersectionFlatMemoKey.input value.referenceOf = some input := by
  cases value with
  | reference reference => cases reference <;> simp_all [identity,Value.referenceOf,IntersectionFlatMemoKey.input]
  | empty | node | mu | union => simp_all [identity,Value.referenceOf,IntersectionFlatMemoKey.input]

/-- An actual Mu query supplies its returned cell and open body provenance without closed operands. -/
theorem request {before after : Checked width} (input : NodeRequest Symbol Guard)
    (fuel : Nat) (result : Value Symbol Guard) (good : Good before) (history : History before)
    (selected : decision input.domain.key input.left input.right = .bothMu ∨
      decision input.domain.key input.left input.right = .leftMu ∨
      decision input.domain.key input.left input.right = .rightMu)
    (actual : Trace fuel (.code (requestNode input.domain input.left input.right)) before (.code (.pure result)) after) :
    History after ∧ Good after ∧ Grows before.native.machine.heap after.native.machine.heap ∧
      ∃ handle, after.native.nodes.cells handle = some ⟨input,.returned result⟩ ∧
        ∃ captured finished count, Good captured ∧ NodeReady captured.native.machine input ∧
          captured.native.nodes.cells handle = some ⟨input,.evaluating⟩ ∧
          Trace count (.code (compileNode input)) captured (.code (.pure result)) finished ∧
          Body after count input captured result finished ∧
          finished.native.nodes.cells handle = some ⟨input,.evaluating⟩ ∧
          Trace 1 (.code (.finishNode handle result (.pure result))) finished (.code (.pure result))
            {finished with native := finishNode handle result finished.native} ∧
          Grows captured.native.machine.heap after.native.machine.heap ∧
          Grows finished.native.machine.heap after.native.machine.heap ∧ Retained finished.native after.native := by
  obtain ⟨reached,checked,growth,origin⟩ := SourceCurrentSharedLeafNativeLineage.request input fuel result good history actual
  obtain ⟨first,second,leftId,rightId⟩ := mu_identities input selected
  obtain ⟨left,leftInput⟩ := identity_keyable input.left first leftId
  obtain ⟨right,rightInput⟩ := identity_keyable input.right second rightId
  have key := IntersectionFlatMemoKeyDomain.sourceKey_complete width input.domain _ _ left right leftInput rightInput
  rcases origin with ⟨unresolved,_⟩ | ⟨handle,present,_⟩
  · change IntersectionFlatMemoKeyDomain.sourceKey width input.domain input.left.referenceOf input.right.referenceOf = none at unresolved
    rw [key] at unresolved
    cases unresolved
  · exact ⟨reached,checked,growth,handle,present,returned reached input result handle present selected⟩

end MicroCFTA.SourceCurrentNativeMuBodyOrigins
