import MicroCFTA.SourceCurrentNativeReferenceOrigins
import MicroCFTA.SourceCurrentNativeActiveQueryForwarding

/-!
# Actual reference body calls at an active reader

The reader map supplies returned child writers without completed History.
The reference read keeps its exact name, binding and operand order.
The supplied historical writer keeps its original checked interval.
-/
namespace MicroCFTA.SourceCurrentNativeActiveReferenceOrigins
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativeSemanticTraceReadback (effects)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceEqualityNativeDemandMemo (Retained)
open SourceCurrentNativeForwardLineage (Forwarded)
open SourceRecursiveIntersectionControl (decision)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A selected reference body retains its exact read and ordered child call at the same reader. -/
theorem trace {before after reader : Checked width}
    (writers : ∀ (handle : Nat) (request : NodeRequest Symbol Guard) (result : Value Symbol Guard),
      reader.native.nodes.cells handle = some ⟨request,.returned result⟩ →
        SourceCurrentNativeWriterReadyRetention.Written handle request result reader.native)
    (request : NodeRequest Symbol Guard) (side : Bool) (fuel : Nat) (result : Value Symbol Guard)
    (good : Good before)
    (actual : Trace fuel (.code (compileNode request)) before (.code (.pure result)) after)
    (retained : Retained after.native reader.native)
    (selected : decision request.domain.key request.left request.right =
      if side then .leftReference else .rightReference) :
    ∃ (name : Nat) (bound : Value Symbol Guard) (childFuel : Nat),
      (if side then request.left else request.right) = .reference (.interned name) ∧
      fuel = childFuel + 1 ∧ childFuel < fuel ∧
      name ∈ SourceRecursiveIntersectionDomain.names request.domain.key ∧
      SourcePreparedSharedRows.read before.native.machine.heap name = some bound ∧
      Trace childFuel (.code (if side then requestNode request.domain bound request.right
        else requestNode request.domain request.left bound)) before (.code (.pure result)) after ∧
      Good after ∧
      Forwarded reader (if side then ⟨request.domain,bound,request.right⟩
        else ⟨request.domain,request.left,bound⟩) before after result := by
  cases side with
  | false =>
    obtain ⟨name,bound,count,shape,total,member,found,child⟩ :=
      SourceCurrentNativeReferenceOrigins.right request fuel result actual selected
    exact ⟨name,bound,count,shape,total,by omega,member,found,child,
      (effects child good (by intro value; trivial)).1,
      SourceCurrentNativeActiveQueryForwarding.forwarded writers
        ⟨request.domain,request.left,bound⟩ count result good child retained⟩
  | true =>
    obtain ⟨name,bound,count,shape,total,member,found,child⟩ :=
      SourceCurrentNativeReferenceOrigins.left request fuel result actual selected
    exact ⟨name,bound,count,shape,total,by omega,member,found,child,
      (effects child good (by intro value; trivial)).1,
      SourceCurrentNativeActiveQueryForwarding.forwarded writers
        ⟨request.domain,bound,request.right⟩ count result good child retained⟩

/-- The supplied historical writer retains its same checked interval and resolved child origin. -/
theorem returned {reader : Checked width}
    (writers : ∀ (handle : Nat) (request : NodeRequest Symbol Guard) (result : Value Symbol Guard),
      reader.native.nodes.cells handle = some ⟨request,.returned result⟩ →
        SourceCurrentNativeWriterReadyRetention.Written handle request result reader.native)
    (request : NodeRequest Symbol Guard) (side : Bool) (result : Value Symbol Guard) (handle : Nat)
    (written : SourceCurrentNativeWriterReadyRetention.Written handle request result reader.native)
    (selected : decision request.domain.key request.left request.right =
      if side then .leftReference else .rightReference) :
    ∃ before after fuel, Good before ∧ NodeReady before.native.machine request ∧
      before.native.nodes.cells handle = some ⟨request,.evaluating⟩ ∧
      Trace fuel (.code (compileNode request)) before (.code (.pure result)) after ∧
      (∃ (name : Nat) (bound : Value Symbol Guard) (childFuel : Nat),
        (if side then request.left else request.right) = .reference (.interned name) ∧
        fuel = childFuel + 1 ∧ childFuel < fuel ∧
        name ∈ SourceRecursiveIntersectionDomain.names request.domain.key ∧
        SourcePreparedSharedRows.read before.native.machine.heap name = some bound ∧
        Trace childFuel (.code (if side then requestNode request.domain bound request.right
          else requestNode request.domain request.left bound)) before (.code (.pure result)) after ∧
        Good after ∧
        Forwarded reader (if side then ⟨request.domain,bound,request.right⟩
          else ⟨request.domain,request.left,bound⟩) before after result) ∧
      after.native.nodes.cells handle = some ⟨request,.evaluating⟩ ∧
      Trace 1 (.code (.finishNode handle result (.pure result))) after (.code (.pure result))
        {after with native := finishNode handle result after.native} ∧
      Grows before.native.machine.heap reader.native.machine.heap ∧
      Grows after.native.machine.heap reader.native.machine.heap ∧ Retained after.native reader.native := by
  obtain ⟨before,after,fuel,good,ready,owner,actual,kept,finish,first,last,retained⟩ := written
  exact ⟨before,after,fuel,good,ready,owner,actual,
    trace writers request side fuel result good actual retained selected,kept,finish,first,last,retained⟩

end MicroCFTA.SourceCurrentNativeActiveReferenceOrigins
