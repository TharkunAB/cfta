import MicroCFTA.SourceCurrentNativeMuStoppingGeneration
import MicroCFTA.SourceCurrentNativeOptionalOwner

/-!
# Captured owners of generated native Mu cells

One stopping-generation application selects the actual optional instruction.
The same returned prefix derives its captured compiler owner and child return.
The result covers yielded and terminal blocked nested construction.
-/
namespace MicroCFTA.SourceCurrentNativeOwnedGeneration
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
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Every new selected Mu keeps its same generating site, captured compiler owner and rooted writer. -/
theorem execute {count : Nat} (request : NodeRequest Symbol Guard) {before : Checked width}
    (inputs : SourceCurrentAllocatedNativePhysicalExecution.InputsThrough count (.code (requestNode request.domain request.left request.right)) before)
    (semantic : SemanticHeap before.native.machine.heap)
    (key : InternedBinderProtocol.NodeKey) (entry : Interned InternedBinderProtocol.NodeKey)
    (body depth ordinary : Value Symbol Guard)
    (selected : (SourceEqualityNativeDemand.execute count (.code (requestNode request.domain request.left request.right)) before).state.native.machine.heap.nodeRecords key =
      some (.mu entry body depth ordinary)) :
    before.native.machine.heap.nodeRecords key = some (.mu entry body depth ordinary) ∨
    ∃ prefixFuel remainingFuel pair siteBody next siteBefore call siteStep,
      count = prefixFuel + 1 + remainingFuel ∧
      Trace prefixFuel (.code (requestNode request.domain request.left request.right)) before (.code (.optionalBinder pair siteBody next)) siteBefore ∧
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
      SourceEqualityNativeDemand.execute count (.code (requestNode request.domain request.left request.right)) before = resume remainingFuel siteStep ∧
      siteBefore.native.machine.heap.nodeRecords key = none ∧
      call.state.nodeRecords key = some (.mu entry body depth ordinary) ∧
      Grows before.native.machine.heap siteBefore.native.machine.heap ∧
      Extends before.native.machine.heap.nodes.issued siteBefore.native.machine.heap.nodes.issued ∧
      Grows call.state (SourceEqualityNativeDemand.execute count (.code (requestNode request.domain request.left request.right)) before).state.native.machine.heap ∧
      Extends call.state.nodes.issued (SourceEqualityNativeDemand.execute count (.code (requestNode request.domain request.left request.right)) before).state.native.machine.heap.nodes.issued ∧
      Reference.intersection pair.1 pair.2 ∈ siteBody.free ∧
      Context siteBefore.native.machine.heap (leaves siteBody) ∧
      InternedFreshOrdinaryConstruction.build
        (.binder true (encode (leaves siteBody) [.intersection pair.1 pair.2] siteBody)) (leaves siteBody)
        siteBefore.native.machine.heap = call ∧
      Written (.binder true (encode (leaves siteBody) [.intersection pair.1 pair.2] siteBody)) (leaves siteBody)
        siteBefore.native.machine.heap call.state key (.mu entry body depth ordinary) ∧
      SourceCurrentNativeOptionalOwnerReceipt.Owner prefixFuel
        (.code (requestNode request.domain request.left request.right)) before pair siteBody next siteBefore := by
  rcases SourceCurrentNativeMuStoppingGeneration.execute inputs semantic key entry body depth ordinary selected with prior | site
  · exact .inl prior
  · obtain ⟨prefixFuel,remainingFuel,pair,siteBody,next,siteBefore,call,siteStep,
      fuelEq,earlierTrace,siteInputs,siteSemantic,siteAvailable,called,mapped,one,resumed,missing,present,
      prefixGrowth,prefixIssued,suffixGrowth,suffixIssued,used,context,built,writer⟩ := site
    have owner := SourceCurrentNativeOptionalOwner.request request prefixFuel before siteBefore
      pair siteBody next earlierTrace
    exact .inr ⟨prefixFuel,remainingFuel,pair,siteBody,next,siteBefore,call,siteStep,
      fuelEq,earlierTrace,siteInputs,siteSemantic,siteAvailable,called,mapped,one,resumed,missing,present,
      prefixGrowth,prefixIssued,suffixGrowth,suffixIssued,used,context,built,writer,owner⟩

end MicroCFTA.SourceCurrentNativeOwnedGeneration
