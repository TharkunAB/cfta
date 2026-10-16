import MicroCFTA.SourceCurrentHereditaryNativeTrace

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
set_option pp.fullNames true

namespace MicroCFTA.HereditaryNativeTraceInductionIndependentChecks
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand SourceEqualityAnnotationLanguage
open SourceCurrentAllocatedRecursivePrefixState
open SourceCurrentAllocatedRecursivePrefixAdmission (Resources)
open SourceCurrentHereditaryNativeTraceInduction (Plain)
open SourceCurrentHereditaryNativeScope (Bindings)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Stored" => SourceCurrentHereditaryNativeControl.Stored Plain
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
variable {bits : Nat} {source : InternedConstructorTemplates.State Symbol Guard}
variable {inventory : List IntersectionFlatMemoKeyDomain.DomainKey}
variable {initial : Cache.State IntersectionFlatMemoKeyDomain.DomainKey}

/-- Initial operand annotations derive the actual body law before its captured owner finishes. -/
theorem completed_body_then_finish
    (resources : Resources bits source inventory initial)
    (request : NodeRequest Symbol Guard) (scope : NodeScope source request) (member : request.domain.key ∈ inventory)
    (before middle : Checked (bits + 2)) (known : Current source inventory initial before)
    (stored : Stored source before) (ready : NodeReady before.native.machine request)
    (bindings : Bindings Plain source request.domain.key)
    (left : Annotated Plain request.left) (right : Annotated Plain request.right)
    (handle fuel : Nat) (running : before.native.nodes.cells handle = some ⟨request, .evaluating⟩)
    (value : Value Symbol Guard)
    (actual : Steps fuel (.code (compileNode request)) before (.code (.pure value)) middle) :
    let finished : Checked (bits + 2) := ⟨finishNode handle value middle.native, middle.operations⟩
    SourceEqualityNativeDemand.step (.code (.finishNode handle value (.pure value))) middle =
        .yielded (.code (.pure value)) finished ∧
      finished.native.nodes.cells handle = some ⟨request, .returned value⟩ ∧
      Stored source finished ∧ Annotated Plain value ∧ SourceMemoGate.unconstrained value = true := by
  have physical := SourceCurrentAllocatedRecursivePrefixCode.node_certified source inventory resources.facts resources.closed
    request scope member before.native.machine known.good.native.machine known.semantic ready known.growth known.history
  have localCertificate := SourceCurrentHereditaryNativeEffectsCompile.node_certified Plain source request bindings
    scope.leftAvailable scope.rightAvailable left right before.native.machine known.good.native.machine stored.constructors ready known.growth known.history
  have fields := SourceCurrentAllocatedNativeCodeFields.compileNode_fields before.operations request
  have result := SourceCurrentHereditaryNativeTrace.completed resources fuel (.code (compileNode request)) before middle value
    (fun state result => Available state.heap result) (fun state result => Available state.heap result ∧ Annotated Plain result)
    known physical fields localCertificate stored actual
  have owner := SourceEqualityNativeDemandProtectedPrefix.node_body_owner fuel handle request before middle value
    known.good.native.shape running actual
  have law := SourceCurrentHereditaryNativeControl.node_law Plain source request value result.2.2
  have finishedStored : Stored source (⟨finishNode handle value middle.native, middle.operations⟩ : Checked (bits + 2)) :=
    ⟨result.1.constructors, SourceCurrentHereditaryNativeCache.finishNode_stored Plain source middle.native handle request value
      result.1.native owner.1 law⟩
  exact ⟨rfl, owner.2, finishedStored, result.2.2, SourceCurrentHereditaryUnconstrained.unconstrained value result.2.2⟩

end MicroCFTA.HereditaryNativeTraceInductionIndependentChecks

#print axioms MicroCFTA.HereditaryNativeTraceInductionIndependentChecks.completed_body_then_finish
#check @MicroCFTA.HereditaryNativeTraceInductionIndependentChecks.completed_body_then_finish
