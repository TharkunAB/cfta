import MicroCFTA.SourceCurrentNativeMuOptionalGeneration
import MicroCFTA.SourceCurrentNativeMuStoppingSite

/-!
# Generated rooted writers at native stopping sites

The actual bounded outcome supplies one optional-binder site. Its same
nested call supplies the generated source build and selected rooted writer.
The call can complete or stop pending. No compiler owner is attached.
-/
namespace MicroCFTA.SourceCurrentNativeMuStoppingGeneration
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedStoredSubstitution (leaves encode)
open InternedBinderProtocol (Reference NodeKey)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentCompletedBuildRootedWriters (Written)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) :=
  SourceEqualityPCSNativeEdge.guardDecidableEq
variable {A : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Every noninitial selected Mu keeps the same generating site, nested outcome and rooted source writer. -/
theorem execute {count : Nat} {control : Control A} {before : Checked width}
    (inputs : SourceCurrentAllocatedNativePhysicalExecution.InputsThrough count control before)
    (semantic : SemanticHeap before.native.machine.heap)
    (key : InternedBinderProtocol.NodeKey) (entry : Interned InternedBinderProtocol.NodeKey)
    (body depth ordinary : Value Symbol Guard)
    (selected : (SourceEqualityNativeDemand.execute count control before).state.native.machine.heap.nodeRecords key =
      some (.mu entry body depth ordinary)) :
    before.native.machine.heap.nodeRecords key = some (.mu entry body depth ordinary) ∨
    ∃ prefixFuel remainingFuel pair siteBody next siteBefore call siteStep,
      count = prefixFuel + 1 + remainingFuel ∧
      Trace prefixFuel control before (.code (.optionalBinder pair siteBody next)) siteBefore ∧
      SourceCurrentAllocatedNativePhysicalExecution.Inputs (.code (.optionalBinder pair siteBody next)) siteBefore ∧
      SemanticHeap siteBefore.native.machine.heap ∧ Available siteBefore.native.machine.heap siteBody ∧
      SourceRecursiveIntersectionMaybeMu.maybeMu pair siteBody siteBefore.native.machine.heap = call ∧
      siteStep = (match call with
        | .done result heap => .yielded (.code (next result))
            ⟨advance siteBefore.native {siteBefore.native.machine with heap := heap},siteBefore.operations⟩
        | .pending pending heap => .blocked (.native (.constructor pending))
            (.code (.optionalBinder pair siteBody next))
            ⟨advance siteBefore.native {siteBefore.native.machine with heap := heap},siteBefore.operations⟩) ∧
      step (.code (.optionalBinder pair siteBody next)) siteBefore = siteStep ∧
      SourceEqualityNativeDemand.execute count control before = resume remainingFuel siteStep ∧
      siteBefore.native.machine.heap.nodeRecords key = none ∧
      call.state.nodeRecords key = some (.mu entry body depth ordinary) ∧
      Grows before.native.machine.heap siteBefore.native.machine.heap ∧
      Extends before.native.machine.heap.nodes.issued siteBefore.native.machine.heap.nodes.issued ∧
      Grows call.state (SourceEqualityNativeDemand.execute count control before).state.native.machine.heap ∧
      Extends call.state.nodes.issued (SourceEqualityNativeDemand.execute count control before).state.native.machine.heap.nodes.issued ∧
      Reference.intersection pair.1 pair.2 ∈ siteBody.free ∧
      Context siteBefore.native.machine.heap (leaves siteBody) ∧
      InternedFreshOrdinaryConstruction.build
        (.binder true (encode (leaves siteBody) [.intersection pair.1 pair.2] siteBody)) (leaves siteBody)
        siteBefore.native.machine.heap = call ∧
      Written (.binder true (encode (leaves siteBody) [.intersection pair.1 pair.2] siteBody)) (leaves siteBody)
        siteBefore.native.machine.heap call.state key (.mu entry body depth ordinary) := by
  rcases SourceCurrentNativeMuStoppingSite.execute inputs semantic key entry body depth ordinary selected with prior | site
  · exact .inl prior
  · obtain ⟨prefixFuel,remainingFuel,pair,siteBody,next,siteBefore,call,siteStep,
      fuelEq,earlierTrace,siteInputs,siteSemantic,siteAvailable,called,mapped,one,resumed,missing,present,
      prefixGrowth,prefixIssued,suffixGrowth,suffixIssued⟩ := site
    have atCall : (SourceRecursiveIntersectionMaybeMu.maybeMu pair siteBody siteBefore.native.machine.heap).state.nodeRecords key =
        some (.mu entry body depth ordinary) := by
      simpa only [called] using present
    rcases SourceCurrentNativeMuOptionalGeneration.maybeMu pair siteBody siteBefore.native.machine.heap
        siteSemantic siteAvailable key entry body depth ordinary atCall with prior | generated
    · rw [missing] at prior
      cases prior
    · obtain ⟨used,context,compiled,written⟩ := generated
      have built := compiled.symm.trans called
      have writer : Written
          (.binder true (encode (leaves siteBody) [.intersection pair.1 pair.2] siteBody)) (leaves siteBody)
          siteBefore.native.machine.heap call.state key (.mu entry body depth ordinary) := by
        simpa only [called] using written
      exact .inr ⟨prefixFuel,remainingFuel,pair,siteBody,next,siteBefore,call,siteStep,
        fuelEq,earlierTrace,siteInputs,siteSemantic,siteAvailable,called,mapped,one,resumed,missing,present,
        prefixGrowth,prefixIssued,suffixGrowth,suffixIssued,used,context,built,writer⟩

end MicroCFTA.SourceCurrentNativeMuStoppingGeneration
