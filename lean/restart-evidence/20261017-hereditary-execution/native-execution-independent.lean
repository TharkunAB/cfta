import MicroCFTA.SourceCurrentHereditaryNativeTrace
import MicroCFTA.SourceCurrentHereditaryNativeControl
import MicroCFTA.SourceCurrentHereditaryNativeTransition

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option format.width 200

namespace MicroCFTA.NativeExecutionReview
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand SourceEqualityAnnotationLanguage
open SourceCurrentHereditaryNativeScope (Bindings)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Native" => SourceRecursiveIntersectionThunks.State
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A warm observed node uses the exact queried owner and the actual full returned state. -/
theorem warm_node (annotation : Guard → Prop) (source : InternedConstructorTemplates.State Symbol Guard)
    (request : NodeRequest Symbol Guard) (before : Checked width) (chosen returned : Native width Symbol Guard)
    (handle : Nat) (value : Value Symbol Guard)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid before.native)
    (stored : SourceCurrentHereditaryNativeControl.Stored annotation source before)
    (ready : NodeReady before.native.machine request)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (bindings : Bindings annotation source request.domain.key)
    (left : Annotated annotation request.left) (right : Annotated annotation request.right)
    (selected : lookupNode width request before.native = (.memoized handle, chosen))
    (demanded : demandNode handle chosen = (.ready value, returned)) :
    let after : Checked width := ⟨returned, before.operations⟩
    SourceEqualityNativeDemand.step (.code (.node request .pure)) before = .yielded (.code (.pure value)) after ∧
      SourceCurrentHereditaryNativeControl.Stored annotation source after ∧
      Available after.native.machine.heap value ∧ Annotated annotation value := by
  dsimp only
  have receipt := SourceCurrentHereditaryNativeCache.node_observed_ready annotation source request before.native chosen returned handle value
    physical stored.native ready safe selected demanded
  have chosenMachine : chosen.machine = before.native.machine := by
    simpa only [selected] using SourceRecursiveIntersectionNative.lookupNode_machine request before.native
  have constructors : SourceCurrentHereditaryConstruction.MuStored annotation returned.machine.heap := by
    rw [receipt.2.2.1, chosenMachine]
    exact stored.constructors
  exact ⟨by simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step, selected, demanded, lift],
    ⟨constructors, receipt.2.1⟩, receipt.2.2.2, receipt.1 bindings left right⟩

/-- A warm observed row retains its full guard and children at the same checked return. -/
theorem warm_edge (annotation : Guard → Prop) (source : InternedConstructorTemplates.State Symbol Guard)
    (request : EdgeRequest Symbol Guard) (before : Checked width) (chosen returned : Native width Symbol Guard)
    (handle : Nat) (value : EdgeValue Symbol Guard)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid before.native)
    (stored : SourceCurrentHereditaryNativeControl.Stored annotation source before)
    (ready : EdgeReady before.native.machine request)
    (safe : SourceRecursiveIntersectionEdgeMemo.KeySafe width request.domain request.left request.right)
    (bindings : Bindings annotation source request.domain.key)
    (left : SourceCurrentHereditaryConstructors.Edge annotation request.left)
    (right : SourceCurrentHereditaryConstructors.Edge annotation request.right)
    (selected : lookupEdge width request before.native = (handle, chosen))
    (demanded : demandEdge handle chosen = (.ready value, returned)) :
    let after : Checked width := ⟨returned, before.operations⟩
    SourceEqualityNativeDemand.step (.code (.edge request .pure)) before = .yielded (.code (.pure value)) after ∧
      SourceCurrentHereditaryNativeControl.Stored annotation source after ∧
      EdgeResident after.native.machine.heap value ∧ SourceCurrentHereditaryConstructors.Edge annotation value := by
  dsimp only
  have receipt := SourceCurrentHereditaryNativeCache.edge_observed_ready annotation source request before.native chosen returned handle value
    physical stored.native ready safe selected demanded
  have chosenMachine : chosen.machine = before.native.machine := by
    simpa only [selected] using SourceRecursiveIntersectionNative.lookupEdge_machine request before.native
  have constructors : SourceCurrentHereditaryConstruction.MuStored annotation returned.machine.heap := by
    rw [receipt.2.2.1, chosenMachine]
    exact stored.constructors
  exact ⟨by simp only [SourceEqualityNativeDemand.step, selected, demanded],
    ⟨constructors, receipt.2.1⟩, receipt.2.2.2, receipt.1 bindings left right⟩

/-- A supplied literal node trace constructs its own local certificates from initial inputs. -/
theorem actual_node_trace {bits fuel : Nat} {source : InternedConstructorTemplates.State Symbol Guard}
    {inventory : List IntersectionFlatMemoKeyDomain.DomainKey} {initial : Cache.State IntersectionFlatMemoKeyDomain.DomainKey}
    (resources : SourceCurrentAllocatedRecursivePrefixAdmission.Resources bits source inventory initial)
    (request : NodeRequest Symbol Guard) (before after : Checked (bits + 2)) (value : Value Symbol Guard)
    (known : SourceCurrentAllocatedRecursivePrefixState.Current source inventory initial before)
    (ready : NodeReady before.native.machine request) (scope : SourceRecursiveIntersectionCode.NodeScope source request)
    (member : request.domain.key ∈ inventory)
    (stored : SourceCurrentHereditaryNativeControl.Stored (fun guard => SourceMemoGate.plain guard = true) source before)
    (bindings : Bindings (fun guard => SourceMemoGate.plain guard = true) source request.domain.key)
    (left : Annotated (fun guard => SourceMemoGate.plain guard = true) request.left)
    (right : Annotated (fun guard => SourceMemoGate.plain guard = true) request.right)
    (actual : SourceEqualityNativeDemand.Steps fuel
      (.code (requestNode request.domain request.left request.right)) before (.code (.pure value)) after) :
    SourceCurrentHereditaryNativeControl.Stored (fun guard => SourceMemoGate.plain guard = true) source after ∧
      Available after.native.machine.heap value ∧ Annotated (fun guard => SourceMemoGate.plain guard = true) value := by
  have physical := SourceCurrentAllocatedRecursivePrefixCode.request_node source inventory request before.native.machine ready scope member
  have localCertificate := SourceCurrentHereditaryNativeEffects.request_node
    (fun guard => SourceMemoGate.plain guard = true) source request before.native.machine bindings left right
  exact SourceCurrentHereditaryNativeTrace.completed resources fuel
    (.code (requestNode request.domain request.left request.right)) before after value
    (fun state result => Available state.heap result)
    (fun state result => Available state.heap result ∧ Annotated (fun guard => SourceMemoGate.plain guard = true) result)
    known physical (by intro _; trivial) localCertificate stored actual

#print axioms warm_node
#check @warm_node
#print axioms warm_edge
#check @warm_edge
#print axioms actual_node_trace
#check @actual_node_trace
end MicroCFTA.NativeExecutionReview

#print axioms MicroCFTA.SourceCurrentHereditaryNativeControl.Certified
#check @MicroCFTA.SourceCurrentHereditaryNativeControl.Certified
#print axioms MicroCFTA.SourceCurrentHereditaryNativeControl.Stored
#check @MicroCFTA.SourceCurrentHereditaryNativeControl.Stored
#print axioms MicroCFTA.SourceCurrentHereditaryNativeControl.pure_result
#check @MicroCFTA.SourceCurrentHereditaryNativeControl.pure_result
#print axioms MicroCFTA.SourceCurrentHereditaryNativeControl.certified_bind
#check @MicroCFTA.SourceCurrentHereditaryNativeControl.certified_bind
#print axioms MicroCFTA.SourceCurrentHereditaryNativeControl.node_law
#check @MicroCFTA.SourceCurrentHereditaryNativeControl.node_law
#print axioms MicroCFTA.SourceCurrentHereditaryNativeControl.edge_law
#check @MicroCFTA.SourceCurrentHereditaryNativeControl.edge_law
#print axioms MicroCFTA.SourceCurrentHereditaryNativeTransition.node_yielded
#check @MicroCFTA.SourceCurrentHereditaryNativeTransition.node_yielded
#print axioms MicroCFTA.SourceCurrentHereditaryNativeTransition.edge_yielded
#check @MicroCFTA.SourceCurrentHereditaryNativeTransition.edge_yielded

#print axioms MicroCFTA.SourceCurrentHereditaryNativeTrace.completed
#check @MicroCFTA.SourceCurrentHereditaryNativeTrace.completed
