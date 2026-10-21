import MicroCFTA.SourceCurrentConstrainedCapCheckedJointInduction
import MicroCFTA.SourceCurrentConstrainedCapCheckedJointCompile
import MicroCFTA.SourceCurrentConstrainedCapCheckedJointEdge
import MicroCFTA.SourceCurrentConstrainedCapCheckedJointTransition
import MicroCFTA.SourceEqualityNativeDemandBodyYield

/-!
# Local hereditary laws over actual completed native traces

Strong induction follows the exact checked trace. Smaller body returns
produce joint conditional laws before their captured finish steps. The supplied
physical trace carries admission at each executed instruction.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapCheckedJointTrace
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentConstrainedCapKernelJoint (Context)
open SourceCurrentConstrainedCapCheckedJointCode (NodeLaw EdgeLaw)
open SourceCurrentAllocatedRecursivePrefixState
open SourceCurrentAllocatedNativeFieldClosure (Fields)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentConstrainedCapCheckedJointInduction (Preserves)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "Physical" => SourceCurrentAllocatedRecursivePrefixControl.Certified
local notation "Certified" => SourceCurrentConstrainedCapCheckedJointControl.Certified Plain
local notation "CodeFields" => SourceCurrentAllocatedNativeCodeFields.Fields
local notation "DomainKey" => IntersectionFlatMemoKeyDomain.DomainKey
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
variable {width : Nat} {source : InternedConstructorTemplates.State Symbol Guard}
variable {inventory : List DomainKey} {initial : Cache.State DomainKey}
local notation "Stored" => SourceCurrentConstrainedCapCheckedJointCache.Stored Plain source

/-- The exact completed trace retains the joint context, causal store, and local output contract. -/
theorem completed (facts : InternedNestedFacts.Facts source)
    (closed : SourceCurrentAllocatedRecursiveDomainCode.Closed source inventory) (fuel : Nat) :
    Preserves source inventory initial width fuel := by
  induction fuel using Nat.strongRecOn with
  | ind count ih =>
    intro A control before after value physicalPost post known physical fields context certificate stored trace
    have admitted := SourceCurrentAllocatedRecursivePrefixControl.entered source inventory control before.native.machine physicalPost physical
    cases count with
    | zero =>
      cases trace
      exact ⟨known, .refl _, SourceEqualityConstraintMemoAllocation.grows_refl _, context, stored,
        SourceCurrentAllocatedRecursivePrefixControl.pure_result source inventory value before.native.machine physicalPost physical,
        SourceCurrentConstrainedCapCheckedJointControl.pure_result Plain source value before.native.machine post certificate⟩
    | succ fuel =>
      cases trace with
      | cons _ _ resume middle _ _ _ inputs one tail =>
        have effects := SourceCurrentAllocatedRecursivePrefixState.yielded control resume before middle known inputs admitted fields one
        have middleContext := SourceCurrentConstrainedCapCheckedJointControl.yielded_context Plain source control resume before middle
          context effects.1 inputs one
        apply SourceCurrentConstrainedCapCheckedJointInduction.Return.prepend effects.2.1 effects.2.2.2.1
        cases control with
        | edgeBody request next =>
          obtain ⟨body, pureBody, same⟩ := SourceEqualityNativeDemandBodyYield.yielded_unbind request next before middle resume one
          subst resume
          have data := SourceCurrentAllocatedRecursivePrefixControl.edge_data source inventory request next before.native.machine physicalPost physical
          have bodyPhysical : Physical source inventory (.code body) middle.native.machine
              (fun final value => EdgeResident final.heap value) :=
            SourceCurrentAllocatedRecursivePrefixCode.body_certified source inventory facts request data.1 data.2.1
              before middle body known.good.native.machine known.semantic data.2.2 pureBody
          have bodyFields := SourceCurrentAllocatedNativeFieldClosure.body_fields request .pure before middle (.code body)
            known.good.fields data.2.2 known.good.operations (fun _ => trivial) pureBody
          have nativeSame : middle.native = before.native := by
            simpa only [pureBody, Outcome.state] using SourceEqualityNativeDemandOperations.body_native request .pure before
          have middleStored : Stored middle.native := by rw [nativeSame]; exact stored
          have bodyCertificate := certificate.1 width before middle body rfl known.good context data.2.2 pureBody
          apply SourceCurrentConstrainedCapCheckedJointInduction.bind (fuel + 1) fuel ih (by omega)
            (.code body) next middle after value _ _ physicalPost post effects.1 middleContext bodyPhysical bodyFields
            (fun result => SourceCurrentAllocatedNativeCodeFields.fields_grows before.operations middle.operations
              (next result) (fields.2 result) effects.2.2.2.1) bodyCertificate middleStored ?_ ?_ tail
          · intro result final current growth resident
            exact SourceCurrentAllocatedRecursivePrefixControl.edge_next source inventory request next before.native.machine physicalPost
              physical result final.native.machine current.good.native.machine (effects.2.1.trans growth) current.semantic resident
          · intro result final current growth finalContext finalStored resident law
            exact certificate.2 result final.native.machine (effects.2.1.trans growth) finalContext resident law
        | code code =>
          cases code with
          | pure | fail => cases one
          | finishNode | finishEdge => cases certificate
          | work job next =>
            obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj one
            have nextPhysical := SourceCurrentAllocatedRecursivePrefixCode.work_next source inventory job next
              before.native.machine physicalPost physical known.semantic _ _ rfl
            have afterStored := SourceCurrentConstrainedCapCheckedJointCache.advance_stored Plain source before.native
              {before.native.machine with heap := (run job before.native.machine.heap).2} stored
            exact ih fuel (by omega) (.code (next (run job before.native.machine.heap).1)) _ after value physicalPost post
              effects.1 nextPhysical.2.2.2 effects.2.2.2.2 middleContext
              (certificate _ _ rfl effects.2.1 middleContext) afterStored tail
          | enter domain left right first second next =>
            obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj one
            have nextPhysical := SourceCurrentAllocatedRecursivePrefixCode.enter_next source inventory domain left right first second next
              before.native.machine physicalPost physical known.semantic
            have afterStored := SourceCurrentConstrainedCapCheckedJointCache.advance_stored Plain source before.native
              {before.native.machine with domains := (SourceRecursiveIntersectionEnvironment.enter
                before.native.machine.domains domain.key left right first second).2} stored
            exact ih fuel (by omega) (.code (next (SourceRecursiveIntersectionEnvironment.enter
              before.native.machine.domains domain.key left right first second).1)) _ after value physicalPost post
              effects.1 nextPhysical.2.2.2 effects.2.2.2.2 middleContext
              (certificate effects.2.1 middleContext) afterStored tail
          | read name next =>
            obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj one
            exact ih fuel (by omega) (.code (next (SourcePreparedSharedRows.read before.native.machine.heap name))) _ after value physicalPost post effects.1
              (SourceCurrentAllocatedRecursivePrefixCode.read_next source inventory name next before.native.machine physicalPost physical)
              effects.2.2.2.2 middleContext certificate stored tail
          | optionalBinder pair body next =>
            cases actual : SourceRecursiveIntersectionMaybeMu.maybeMu pair body before.native.machine.heap with
            | pending key heap =>
                simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step, actual, lift] at one
                cases one
            | done result heap =>
                simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step, actual, lift] at one
                obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj one
                have done : construction (SourceRecursiveIntersectionMaybeMu.maybeMu pair body before.native.machine.heap)
                    before.native.machine = .done result {before.native.machine with heap := heap} := by rw [actual]; rfl
                have nextPhysical := SourceCurrentAllocatedRecursivePrefixCode.optionalBinder_next source inventory pair body next
                  before.native.machine physicalPost physical known.semantic _ _ done
                have afterStored := SourceCurrentConstrainedCapCheckedJointCache.advance_stored Plain source before.native
                  {before.native.machine with heap := heap} stored
                exact ih fuel (by omega) (.code (next result)) _ after value physicalPost post effects.1
                  nextPhysical.2.2.2 effects.2.2.2.2 middleContext
                  (certificate _ _ done effects.2.1 middleContext) afterStored tail
          | node request next =>
            have data := SourceCurrentAllocatedRecursivePrefixCode.node_data source inventory request next before.native.machine physicalPost physical
            have words := inputs.2
            obtain ⟨machine, operations, _nativeStored, branches⟩ := SourceCurrentConstrainedCapCheckedJointTransition.node_yielded Plain source request next
              before resume middle known.good.native stored data.1 words one
            have middleStored := _nativeStored
            have ready : NodeReady middle.native.machine request := by rw [machine]; exact data.1
            have bodyPhysical := SourceCurrentAllocatedRecursivePrefixCode.node_certified source inventory facts closed
              request data.2.1 data.2.2 middle.native.machine effects.1.good.native.machine effects.1.semantic ready effects.1.growth effects.1.history
            have bodyCertificate := SourceCurrentConstrainedCapCheckedJointCompile.node_law_certified Plain source facts request
              middle.native.machine middleContext ready.1
            have bodyFields := SourceCurrentAllocatedNativeCodeFields.compileNode_fields middle.operations request
            have nextFields : ∀ result, CodeFields middle.operations (next result) := by rw [operations]; exact fields
            have continuation : ∀ result (final : Checked width), Current source inventory initial final →
                Extension middle.native.machine final.native.machine → Available final.native.machine.heap result →
                Physical source inventory (.code (next result)) final.native.machine physicalPost := by
              intro result final current growth available
              exact SourceCurrentAllocatedRecursivePrefixCode.node_next source inventory request next before.native.machine physicalPost
                physical result final.native.machine current.good.native.machine (effects.2.1.trans growth) current.semantic available
            have localNext : ∀ result (final : Checked width), Current source inventory initial final →
                Extension middle.native.machine final.native.machine → Context Plain source final.native.machine → Stored final.native →
                Available final.native.machine.heap result → NodeLaw Plain source request result →
                Certified source (.code (next result)) final.native.machine post := by
              intro result final current growth finalContext finalStored available law
              exact certificate result final.native.machine (effects.2.1.trans growth) finalContext available law
            rcases branches with ⟨rfl, _⟩ | ⟨result, rfl, available, law⟩ | ⟨handle, rfl, running⟩
            · exact SourceCurrentConstrainedCapCheckedJointInduction.bind (fuel + 1) fuel ih (by omega)
                (.code (compileNode request)) next middle after value _ _ physicalPost post effects.1 middleContext bodyPhysical bodyFields nextFields
                bodyCertificate middleStored continuation localNext tail
            · exact ih fuel (by omega) _ middle after value physicalPost post effects.1
                (continuation result middle effects.1 (.refl _) available) (nextFields result) middleContext
                (certificate result middle.native.machine effects.2.1 middleContext available law)
                middleStored tail
            · exact SourceCurrentConstrainedCapCheckedJointInduction.node_bind (fuel + 1) fuel handle ih (by omega)
                request next middle after value physicalPost post effects.1 middleContext bodyPhysical bodyFields nextFields
                bodyCertificate middleStored running continuation localNext tail
          | edge request next =>
            have data := SourceCurrentAllocatedRecursivePrefixCode.edge_data source inventory request next before.native.machine physicalPost physical
            have words := inputs.2
            obtain ⟨machine, operations, _nativeStored, branches⟩ := SourceCurrentConstrainedCapCheckedJointTransition.edge_yielded Plain source request next
              before resume middle known.good.native stored data.1 words one
            have middleStored := _nativeStored
            have ready : EdgeReady middle.native.machine request := by rw [machine]; exact data.1
            have bodyPhysical := SourceCurrentAllocatedRecursivePrefixControl.edge_body source inventory request
              middle.native.machine data.2.1 data.2.2 ready
            have bodyCertificate : Certified source (.edgeBody request .pure) middle.native.machine
                (fun _ result => EdgeLaw Plain source request result) :=
              ⟨by
                intro width before after body same good context ready yielded
                rw [← same] at context ready
                exact SourceCurrentConstrainedCapCheckedJointEdge.body_law_certified source request before after body
                  good context ready yielded,
                fun _ _ _ _ _ law => law⟩
            have bodyFields : Fields (.edgeBody request .pure) middle := ⟨ready, fun _ => trivial⟩
            have nextFields : ∀ result, CodeFields middle.operations (next result) := by rw [operations]; exact fields
            have continuation : ∀ result (final : Checked width), Current source inventory initial final →
                Extension middle.native.machine final.native.machine → EdgeResident final.native.machine.heap result →
                Physical source inventory (.code (next result)) final.native.machine physicalPost := by
              intro result final current growth resident
              exact SourceCurrentAllocatedRecursivePrefixCode.edge_next source inventory request next before.native.machine physicalPost
                physical result final.native.machine current.good.native.machine (effects.2.1.trans growth) current.semantic resident
            have localNext : ∀ result (final : Checked width), Current source inventory initial final →
                Extension middle.native.machine final.native.machine → Context Plain source final.native.machine → Stored final.native →
                EdgeResident final.native.machine.heap result → EdgeLaw Plain source request result →
                Certified source (.code (next result)) final.native.machine post := by
              intro result final current growth finalContext finalStored resident law
              exact certificate result final.native.machine (effects.2.1.trans growth) finalContext resident law
            rcases branches with ⟨result, rfl, resident, law⟩ | ⟨handle, rfl, running⟩
            · exact ih fuel (by omega) _ middle after value physicalPost post effects.1
                (continuation result middle effects.1 (.refl _) resident) (nextFields result) middleContext
                (certificate result middle.native.machine effects.2.1 middleContext resident law)
                middleStored tail
            · exact SourceCurrentConstrainedCapCheckedJointInduction.edge_bind (fuel + 1) fuel handle ih (by omega)
                request next middle after value physicalPost post effects.1 middleContext bodyPhysical bodyFields nextFields
                bodyCertificate middleStored running continuation localNext tail

end MicroCFTA.SourceCurrentConstrainedCapCheckedJointTrace
