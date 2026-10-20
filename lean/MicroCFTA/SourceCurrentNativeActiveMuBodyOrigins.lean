import MicroCFTA.SourceCurrentNativeMuBodyOrigins
import MicroCFTA.SourceCurrentNativeActiveQueryForwarding

/-!
# Actual Mu body calls at an active reader

The reader map supplies returned child writers without completed History.
The chosen historical writer keeps its exact domain entry, body call and
optional construction. No History is assigned to the active child entry.
-/
namespace MicroCFTA.SourceCurrentNativeActiveMuBodyOrigins
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativeSemanticTraceReadback (current_inputs effects)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceEqualityNativeDemandMemo (Retained)
open SourceRecursiveIntersectionControl (decision identity pair)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat}

open SourceCurrentNativeMuBodyOrigins (Body)

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A completed Mu body derives its checked open child entry and exact request origin. -/
theorem trace {before after reader : Checked width} (writers : ∀ (handle : Nat) (request : NodeRequest Symbol Guard) (result : Value Symbol Guard),
      reader.native.nodes.cells handle = some ⟨request,.returned result⟩ →
        SourceCurrentNativeWriterReadyRetention.Written handle request result reader.native)
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
  have origin := SourceCurrentNativeActiveQueryForwarding.forwarded writers
    ⟨_,body request.left,body request.right⟩ childFuel bodyValue reached.1 child middleRetained
  exact ⟨first,second,childFuel,bodyValue,middle,heap,leftId,rightId,count,reached.1,
    child,middleGood,origin,available,binder,final⟩

/-- The selected historical writer retains its same captured owner and actual open body call. -/
theorem returned {reader : Checked width} (writers : ∀ (handle : Nat) (request : NodeRequest Symbol Guard) (result : Value Symbol Guard),
      reader.native.nodes.cells handle = some ⟨request,.returned result⟩ →
        SourceCurrentNativeWriterReadyRetention.Written handle request result reader.native)
    (request : NodeRequest Symbol Guard) (result : Value Symbol Guard) (handle : Nat)
    (written : SourceCurrentNativeWriterReadyRetention.Written handle request result reader.native)
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
    written
  have compiled : compileNode request = compileMu request.domain request.left request.right := by
    rcases selected with selected | selected | selected <;> simp only [compileNode,selected]
  exact ⟨before,after,fuel,good,ready,owner,actual,
    trace writers request fuel result good (compiled ▸ actual) retained,kept,finish,first,last,retained⟩

end MicroCFTA.SourceCurrentNativeActiveMuBodyOrigins
