import MicroCFTA.SourceCurrentAllocatedRecursiveRequestStep

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
set_option pp.fullNames true

namespace MicroCFTA.RecursiveRequestStepChecks
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceCurrentAllocatedRecursiveRequestStep
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- Actual miss publication yields an evaluating original owner before any recursive body executes. -/
theorem fresh_node_frame [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request : NodeRequest Symbol Guard) (next : Value Symbol Guard → Code Symbol Guard A)
    (before : SourceEqualityNativeDemand.State width)
    (valid : SourceCurrentAllocatedNativePhysicalCache.Valid before.native)
    (ready : NodeReady before.native.machine request)
    (words : SourceCurrentAllocatedNativeRequestBounds.Words width (.code (.node request next)))
    (key : IntersectionFlatMemoKeyDomain.Triple width)
    (encoded : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key)
    (missing : before.native.nodes.table key = none) :
    let handle := before.native.nodes.next
    let chosen := (lookupNode width request before.native).2
    let running := (demandNode handle chosen).2
    let after : SourceEqualityNativeDemand.State width := ⟨running, before.operations⟩
    SourceEqualityNativeDemand.step (.code (.node request next)) before =
      .yielded (.code ((compileNode request).bind (fun value => .finishNode handle value (next value)))) after ∧
      after.native.machine = before.native.machine ∧ after.operations = before.operations ∧
      after.native.nodes.cells handle = some ⟨request, .evaluating⟩ := by
  let handle := before.native.nodes.next
  let chosen := (lookupNode width request before.native).2
  let running := (demandNode handle chosen).2
  let after : SourceEqualityNativeDemand.State width := ⟨running, before.operations⟩
  have selected : lookupNode width request before.native = (.memoized handle, chosen) := by
    simp [chosen, handle, lookupNode, encoded, FlatMemoThunk.lookupOrInsert, missing]
  have demanded : demandNode handle chosen = (.evaluate request, running) := by
    apply Prod.ext
    · simp [chosen, handle, lookupNode, encoded, FlatMemoThunk.lookupOrInsert, missing,
        demandNode, FlatMemoThunk.demand, Cache.put]
    · rfl
  have yielded : SourceEqualityNativeDemand.step (.code (.node request next)) before =
      .yielded (.code ((compileNode request).bind (fun value => .finishNode handle value (next value)))) after := by
    simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step, selected, demanded,
      SourceEqualityNativeDemand.lift]
    rfl
  have classified := node_yielded request next before _ after valid ready words yielded
  exact ⟨yielded, classified.1, classified.2.1,
    (SourceRecursiveIntersectionNative.demandNode_evaluate handle chosen running request demanded).2⟩

/-- A physically valid returned edge gives a literal warm continuation with no body replay. -/
theorem warm_edge_continuation [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request : EdgeRequest Symbol Guard) (next : EdgeValue Symbol Guard → Code Symbol Guard A)
    (before : SourceEqualityNativeDemand.State width)
    (valid : SourceCurrentAllocatedNativePhysicalCache.Valid before.native)
    (ready : EdgeReady before.native.machine request)
    (words : SourceCurrentAllocatedNativeRequestBounds.Words width (.code (.edge request next)))
    (handle : Nat) (value : EdgeValue Symbol Guard)
    (published : before.native.edges.table
      (SourceRecursiveIntersectionEdgeMemo.requestKey width request.domain request.left request.right) = some handle)
    (stored : before.native.edges.cells handle = some ⟨request, .returned value⟩) :
    SourceEqualityNativeDemand.step (.code (.edge request next)) before = .yielded (.code (next value)) before ∧
      EdgeResident before.native.machine.heap value ∧ before.operations = before.operations := by
  have receipt := SourceCurrentAllocatedNativePhysicalCache.edge_ready_receipt before.native valid request request ready
    _ ⟨rfl, words⟩ handle published value stored
  have yielded : SourceEqualityNativeDemand.step (.code (.edge request next)) before = .yielded (.code (next value)) before := by
    simp only [SourceEqualityNativeDemand.step, receipt.2.1, receipt.2.2.1]
  have classified := edge_yielded request next before _ before valid ready words yielded
  exact ⟨yielded, receipt.2.2.2, classified.2.1⟩

/-- Optional-key bypass yields the original compiled request with the entire state unchanged. -/
theorem direct_node_state [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request : NodeRequest Symbol Guard) (next : Value Symbol Guard → Code Symbol Guard A)
    (before : SourceEqualityNativeDemand.State width)
    (bypass : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = none) :
    SourceEqualityNativeDemand.step (.code (.node request next)) before =
      .yielded (.code ((compileNode request).bind next)) before := by
  simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step, lookupNode, bypass,
    SourceEqualityNativeDemand.lift]

#print axioms fresh_node_frame
#check @fresh_node_frame
#print axioms warm_edge_continuation
#check @warm_edge_continuation
#print axioms direct_node_state
#check @direct_node_state
end MicroCFTA.RecursiveRequestStepChecks
