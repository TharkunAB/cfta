import MicroCFTA.SourceCurrentNativeQueryRowOrigins
import MicroCFTA.SourceCurrentAllocatedNativeMuSource

/-!
# Actual captured Mu body and binder schedules

The completed captured writer supplies its literal entered body request.
The optional binder retains its actual input and full returned state.
This result does not infer an earlier Mu publication history or identify
the current callback with a retained earlier writer.
-/
namespace MicroCFTA.SourceCurrentNativeMuWriterOrigins
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativeSemanticTraceReadback (after_step bind_inverse current_inputs)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentNativeEdgeWriterGrowth (History)
open SourceCurrentNativeWriterReadyRetention (Written)
open SourceRecursiveIntersectionControl (decision identity pair)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A captured Mu body retains the exact entered request and subsequent binder outcome. -/
def Schedule (fuel : Nat) (request : NodeRequest Symbol Guard)
    (before : Checked width) (result : Value Symbol Guard) (after : Checked width) : Prop :=
  ∃ first second childFuel bodyValue middle heap,
    let entered := SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains request.domain.key
      request.left request.right first second
    identity request.left = some first ∧ identity request.right = some second ∧
    fuel = childFuel + 2 ∧
    Trace childFuel (.code (requestNode entered.1 (body request.left) (body request.right)))
      {before with native := advance before.native {before.native.machine with domains := entered.2}}
      (.code (.pure bodyValue)) middle ∧
    Available middle.native.machine.heap bodyValue ∧
    SourceRecursiveIntersectionMaybeMu.maybeMu (pair first second) bodyValue middle.native.machine.heap =
      .done result heap ∧
    after = {middle with native := advance middle.native {middle.native.machine with heap := heap}} ∧
    (.intersection (pair first second).1 (pair first second).2 ∉ bodyValue.free →
      result = bodyValue ∧ heap = middle.native.machine.heap)

private theorem failed_body (failure : SourceRecursiveIntersectionKernel.Failure)
    (actual : Trace fuel (.code (.fail failure)) before (.code (.pure result)) after) : False := by
  cases actual with
  | cons _ _ _ _ _ _ _ _ one _ => cases one

private theorem optional_readback (key : Nat × Nat) (bodyValue : Value Symbol Guard)
    (fuel : Nat) (before after : Checked width) (result : Value Symbol Guard)
    (actual : Trace fuel (.code (.optionalBinder key bodyValue .pure)) before (.code (.pure result)) after) :
    ∃ heap, fuel = 1 ∧ Available before.native.machine.heap bodyValue ∧
      SourceRecursiveIntersectionMaybeMu.maybeMu key bodyValue before.native.machine.heap = .done result heap ∧
      after = {before with native := advance before.native {before.native.machine with heap := heap}} ∧
      (.intersection key.1 key.2 ∉ bodyValue.free → result = bodyValue ∧ heap = before.native.machine.heap) := by
  have available := current_inputs actual
  cases observed : SourceRecursiveIntersectionMaybeMu.maybeMu key bodyValue before.native.machine.heap with
  | pending name heap =>
    cases actual with
    | cons _ _ _ _ _ _ _ _ one _ =>
      simp only [step, SourceRecursiveIntersectionNative.step, observed, lift] at one
      cases one
  | done value heap =>
    have one : step (.code (.optionalBinder key bodyValue .pure)) before =
        .yielded (.code (.pure value))
          {before with native := advance before.native {before.native.machine with heap := heap}} := by
      simp only [step,SourceRecursiveIntersectionNative.step,observed,lift]
    obtain ⟨count,total,rest⟩ := after_step fuel _ _ before _ after result actual one
    obtain ⟨rfl,same,retained⟩ := pure_trace count value result _ after rest.steps
    subst result
    refine ⟨heap,total,available,rfl,retained.symm,?_⟩
    intro unused
    have equal := observed
    simp only [SourceRecursiveIntersectionMaybeMu.maybeMu,unused,ite_false] at equal
    exact ⟨(InternedNestedConstruction.Outcome.done.inj equal).1.symm,
      (InternedNestedConstruction.Outcome.done.inj equal).2.symm⟩

/-- A completed literal Mu compiler body derives its actual child request and binder endpoint. -/
theorem trace (request : NodeRequest Symbol Guard) (fuel : Nat)
    (before after : Checked width) (result : Value Symbol Guard)
    (actual : Trace fuel (.code (compileMu request.domain request.left request.right)) before (.code (.pure result)) after) :
    Schedule fuel request before result after := by
  cases first : identity request.left with
  | none =>
    simp only [compileMu,first,SourceRecursiveIntersectionCode.unsupported] at actual
    exact False.elim (failed_body _ actual)
  | some left =>
    cases second : identity request.right with
    | none =>
      simp only [compileMu,first,second,SourceRecursiveIntersectionCode.unsupported] at actual
      exact False.elim (failed_body _ actual)
    | some right =>
      have one := SourceCurrentAllocatedNativeMuSource.enter_prefix request before left right first second
      obtain ⟨restFuel,total,rest⟩ := after_step fuel _ _ before _ after result actual one
      obtain ⟨childFuel,tailFuel,bodyValue,middle,count,child,tail⟩ := bind_inverse restFuel
        (.code (requestNode
          (SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains request.domain.key
            request.left request.right left right).1 (body request.left) (body request.right)))
        (fun value => .optionalBinder (pair left right) value .pure) _ after result rest
      obtain ⟨heap,tailCount,available,binder,final,unused⟩ := optional_readback _ _ tailFuel middle after result tail
      exact ⟨left,right,childFuel,bodyValue,middle,heap,first,second,(by omega),child,available,binder,final,unused⟩

/-- A returned selected Mu branch retains its exact captured writer and the derived internal schedule. -/
theorem returned {reader : Checked width} (history : History reader)
    (request : NodeRequest Symbol Guard) (result : Value Symbol Guard) (handle : Nat)
    (present : reader.native.nodes.cells handle = some ⟨request,.returned result⟩)
    (selected : decision request.domain.key request.left request.right = .bothMu ∨
      decision request.domain.key request.left request.right = .leftMu ∨
      decision request.domain.key request.left request.right = .rightMu) :
    ∃ before after fuel, Good before ∧ NodeReady before.native.machine request ∧
      before.native.nodes.cells handle = some ⟨request,.evaluating⟩ ∧
      Trace fuel (.code (compileNode request)) before (.code (.pure result)) after ∧
      Schedule fuel request before result after ∧
      after.native.nodes.cells handle = some ⟨request,.evaluating⟩ ∧
      Grows before.native.machine.heap reader.native.machine.heap ∧
      Grows after.native.machine.heap reader.native.machine.heap ∧
      SourceEqualityNativeDemandMemo.Retained after.native reader.native := by
  obtain ⟨before,after,fuel,good,ready,owner,actual,kept,_finished,first,last,retained⟩ :=
    SourceCurrentNativeWriterReadyRetention.writers history handle request result present
  have compiled : compileNode request = compileMu request.domain request.left request.right := by
    rcases selected with selected | selected | selected <;> simp only [compileNode,selected]
  have scheduled := trace request fuel before after result (compiled ▸ actual)
  exact ⟨before,after,fuel,good,ready,owner,actual,scheduled,kept,first,last,retained⟩

end MicroCFTA.SourceCurrentNativeMuWriterOrigins
