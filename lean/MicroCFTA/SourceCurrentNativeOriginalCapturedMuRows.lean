import MicroCFTA.SourceCurrentNativeRootedMuStoredRows
import MicroCFTA.SourceCurrentNativeCapturedMuUnfoldRows

/-!
# Original source rows of an initial captured Mu

The original closed build returns exactly the native entry heap.
An initial captured Mu retains that source program's fixed publication.
The actual earlier generated alternative remains unchanged.
-/
namespace MicroCFTA.SourceCurrentNativeOriginalCapturedMuRows
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedStoredSubstitution (leaves encode)
open InternedBinderProtocol (Reference NodeKey)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentCompletedBuildRootedWriters (Written)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentNativeEdgeWriterGrowth (History)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
variable {width : Nat}
variable [DecidableEq (EdgeKey Symbol Guard)]

open SourceCurrentNativeCapturedMuStoredRows (Stored)

open SourceCurrentNativeCapturedMuUnfoldRows (Observed)
variable [DecidableEq Symbol]

/-- Actual source construction attaches the same initial captured Mu to its original fixed callback. -/
theorem capture_source (original : Syntax Symbol Guard) (root : Node) (request : NodeRequest Symbol Guard) (fuel : Nat) (before current : Checked width)
    (pair : Nat × Nat) (siteBody : Node) (siteNext : Node → Code Symbol Guard Node)
    (sourceBuild : InternedFreshOrdinaryConstruction.build original [] empty =
      .done root before.native.machine.heap)
    (good : Good before) (history : History before)
    (actual : Trace fuel (.code (requestNode request.domain request.left request.right)) before
      (.code (.optionalBinder pair siteBody siteNext)) current)
    (available : Available current.native.machine.heap siteBody)
    (index : Nat) (entry : Interned NodeKey) (body depth ordinary : Node)
    (found : (leaves siteBody)[index]? = some (.mu entry body depth ordinary)) :
    (before.native.machine.heap.nodeRecords entry.key = some (.mu entry body depth ordinary) ∧
      Observed original [] empty before.native.machine.heap entry.key entry body depth ordinary
        current.native.machine.heap) ∨
    ∃ prefixFuel suffixFuel priorPair parent next siteBefore siteAfter result heap,
      fuel = prefixFuel + 1 + suffixFuel ∧ prefixFuel < fuel ∧
      Trace prefixFuel (.code (requestNode request.domain request.left request.right)) before
        (.code (.optionalBinder priorPair parent next)) siteBefore ∧
      SemanticHeap siteBefore.native.machine.heap ∧ Available siteBefore.native.machine.heap parent ∧
      SourceRecursiveIntersectionMaybeMu.maybeMu priorPair parent siteBefore.native.machine.heap = .done result heap ∧
      siteAfter = ⟨advance siteBefore.native {siteBefore.native.machine with heap := heap},siteBefore.operations⟩ ∧
      step (.code (.optionalBinder priorPair parent next)) siteBefore = .yielded (.code (next result)) siteAfter ∧
      Trace suffixFuel (.code (next result)) siteAfter (.code (.optionalBinder pair siteBody siteNext)) current ∧
      siteBefore.native.machine.heap.nodeRecords entry.key = none ∧
      heap.nodeRecords entry.key = some (.mu entry body depth ordinary) ∧
      Grows before.native.machine.heap siteBefore.native.machine.heap ∧
      Extends before.native.machine.heap.nodes.issued siteBefore.native.machine.heap.nodes.issued ∧
      Grows heap current.native.machine.heap ∧ Extends heap.nodes.issued current.native.machine.heap.nodes.issued ∧
      Reference.intersection priorPair.1 priorPair.2 ∈ parent.free ∧
      Context siteBefore.native.machine.heap (leaves parent) ∧
      InternedFreshOrdinaryConstruction.build
        (.binder true (encode (leaves parent) [.intersection priorPair.1 priorPair.2] parent)) (leaves parent)
        siteBefore.native.machine.heap = .done result heap ∧
      Written (.binder true (encode (leaves parent) [.intersection priorPair.1 priorPair.2] parent)) (leaves parent)
        siteBefore.native.machine.heap heap entry.key (.mu entry body depth ordinary) ∧
      SourceCurrentNativeOptionalRowProduction.Origin request prefixFuel before siteBefore priorPair parent next ∧
      Stored (.binder true (encode (leaves parent) [.intersection priorPair.1 priorPair.2] parent))
        (leaves parent) siteBefore.native.machine.heap heap entry.key entry body depth ordinary ∧
      Observed (.binder true (encode (leaves parent) [.intersection priorPair.1 priorPair.2] parent))
        (leaves parent) siteBefore.native.machine.heap heap entry.key entry body depth ordinary
        current.native.machine.heap := by
  have semantic := SourceRecursiveIntersectionSemanticHeap.constructed original root before.native.machine.heap sourceBuild
  have publications : SourceCurrentNativeMuPublication.History empty before.native.machine.heap := by
    simpa only [sourceBuild,InternedNestedConstruction.Outcome.state] using
      SourceCurrentNativeMuPublication.closed_history original
  rcases SourceCurrentNativeCapturedMuUnfoldRows.capture request fuel before current pair siteBody siteNext
      good history semantic publications actual available index entry body depth ordinary found with prior | generated
  · have written := SourceCurrentCompletedBuildRootedWriters.build_writer original [] empty
      SourceCurrentConstrainedCapSourceHistory.empty_context
      (by intro key selected storedBody storedDepth storedOrdinary impossible; cases impossible)
      root before.native.machine.heap sourceBuild entry.key entry body depth ordinary prior
    have stored := SourceCurrentNativeRootedMuStoredRows.of_written original [] empty
      before.native.machine.heap entry.key entry body depth ordinary written
    have captured := InternedStoredSubstitution.leaves_available siteBody current.native.machine.heap available
      (.mu entry body depth ordinary) (List.mem_of_getElem? found)
    obtain ⟨currentSemantic,⟨published⟩⟩ := SourceCurrentNativePublicationTrace.from_history actual semantic publications
    exact .inl ⟨prior,SourceCurrentNativeCapturedMuUnfoldRows.observe original [] empty
      before.native.machine.heap entry.key entry body depth ordinary stored current.native.machine.heap
      currentSemantic captured published⟩
  · exact .inr generated

end MicroCFTA.SourceCurrentNativeOriginalCapturedMuRows
