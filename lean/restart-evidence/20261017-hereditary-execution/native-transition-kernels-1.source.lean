import MicroCFTA.SourceCurrentHereditaryNativeTransition

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
set_option pp.fullNames true

namespace MicroCFTA.HereditaryNativeTransitionIndependentChecks
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceCurrentHereditaryNativeCode (NodeLaw EdgeLaw)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A genuine absent key publishes and starts its own owner before any body result exists. -/
theorem fresh_node (annotation : Guard → Prop) (source : InternedConstructorTemplates.State Symbol Guard)
    (request : NodeRequest Symbol Guard) (before : Checked width)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid before.native)
    (stored : SourceCurrentHereditaryNativeCache.Stored annotation source before.native)
    (ready : NodeReady before.native.machine request)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (key : IntersectionFlatMemoKeyDomain.Triple width)
    (encoded : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key)
    (missing : before.native.nodes.table key = none) :
    ∃ after, SourceEqualityNativeDemand.step (.code (.node request Code.pure)) before =
        .yielded (.code ((compileNode request).bind (fun value => .finishNode before.native.nodes.next value (.pure value)))) after ∧
      after.native.nodes.cells before.native.nodes.next = some ⟨request, .evaluating⟩ ∧
      SourceCurrentHereditaryNativeCache.Stored annotation source after.native ∧
      after.native.machine = before.native.machine ∧ after.operations = before.operations := by
  let handle := before.native.nodes.next
  let chosen := (lookupNode width request before.native).2
  let running := (demandNode handle chosen).2
  have selected : lookupNode width request before.native = (.memoized handle, chosen) := by
    simp [chosen, handle, lookupNode, encoded, FlatMemoThunk.lookupOrInsert, missing]
  have demanded : demandNode handle chosen = (.evaluate request, running) := by
    apply Prod.ext
    · simp [chosen, handle, lookupNode, encoded, FlatMemoThunk.lookupOrInsert, missing, demandNode, FlatMemoThunk.demand, Cache.put]
    · rfl
  let after : Checked width := ⟨running, before.operations⟩
  have yielded : SourceEqualityNativeDemand.step (.code (.node request Code.pure)) before =
      .yielded (.code ((compileNode request).bind (fun value => .finishNode handle value (.pure value)))) after := by
    simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step, selected, demanded, SourceEqualityNativeDemand.lift]
    rfl
  have words : SourceCurrentAllocatedNativeRequestBounds.Words width (.code (.node request Code.pure)) := fun _ _ => safe
  have checked := SourceCurrentHereditaryNativeTransition.node_yielded annotation source request Code.pure before _ after
    physical stored ready words yielded
  have owner := (SourceRecursiveIntersectionNative.demandNode_evaluate handle chosen running request demanded).2
  exact ⟨after, yielded, owner, checked.2.2.1, checked.1, checked.2.1⟩

/-- An exact resident warm row returns its local law without a body or equality operation. -/
theorem warm_edge (annotation : Guard → Prop) (source : InternedConstructorTemplates.State Symbol Guard)
    (request original : EdgeRequest Symbol Guard) (before : Checked width)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid before.native)
    (stored : SourceCurrentHereditaryNativeCache.Stored annotation source before.native)
    (ready : EdgeReady before.native.machine request)
    (safe : SourceRecursiveIntersectionEdgeMemo.KeySafe width request.domain request.left request.right)
    (handle : Nat) (value : EdgeValue Symbol Guard)
    (published : before.native.edges.table (SourceRecursiveIntersectionEdgeMemo.requestKey width request.domain request.left request.right) = some handle)
    (returned : before.native.edges.cells handle = some ⟨original, .returned value⟩) :
    SourceEqualityNativeDemand.step (.code (.edge request Code.pure)) before = .yielded (.code (.pure value)) before ∧
      SourceCurrentHereditaryNativeCache.Stored annotation source before.native ∧
      EdgeLaw annotation source request value ∧ EdgeResident before.native.machine.heap value := by
  have receipt := SourceCurrentAllocatedNativePhysicalCache.edge_ready_receipt before.native physical request original ready
    _ ⟨rfl, safe⟩ handle published value returned
  have yielded : SourceEqualityNativeDemand.step (.code (.edge request Code.pure)) before = .yielded (.code (.pure value)) before := by
    simp only [SourceEqualityNativeDemand.step, receipt.2.1, receipt.2.2.1]
  have checked := SourceCurrentHereditaryNativeTransition.edge_yielded annotation source request Code.pure before _ before
    physical stored ready safe yielded
  have localLaw := SourceCurrentHereditaryNativeCache.edge_observed_ready annotation source request before.native before.native before.native
    handle value physical stored ready safe receipt.2.1 receipt.2.2.1
  exact ⟨yielded, checked.2.2.1, localLaw.1, localLaw.2.2.2⟩

end MicroCFTA.HereditaryNativeTransitionIndependentChecks

#print axioms MicroCFTA.HereditaryNativeTransitionIndependentChecks.fresh_node
#check @MicroCFTA.HereditaryNativeTransitionIndependentChecks.fresh_node
#print axioms MicroCFTA.HereditaryNativeTransitionIndependentChecks.warm_edge
#check @MicroCFTA.HereditaryNativeTransitionIndependentChecks.warm_edge
