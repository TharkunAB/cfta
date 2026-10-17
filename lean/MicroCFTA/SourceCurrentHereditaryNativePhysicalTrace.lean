import MicroCFTA.SourceCurrentHereditaryNativePhysicalInduction
import MicroCFTA.SourceCurrentHereditaryNativeEffectsCompile
import MicroCFTA.SourceCurrentHereditaryNativeEffectsEdge
import MicroCFTA.SourceCurrentHereditaryNativeTransition

/-!
# Local hereditary laws over actual completed native traces

Strong induction follows the exact checked trace. Smaller body returns
produce local annotations before their captured finish steps. The supplied
physical trace carries admission at each executed instruction.
-/
namespace MicroCFTA.SourceCurrentHereditaryNativePhysicalTrace
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand SourceEqualityAnnotationLanguage
open SourceCurrentAllocatedRecursivePrefixState
open SourceCurrentAllocatedNativeFieldClosure (Fields)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentHereditaryNativePhysicalInduction (Preserves)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "Physical" => SourceCurrentAllocatedRecursivePrefixControl.Certified
local notation "Certified" => SourceCurrentHereditaryNativeControl.Certified Plain
local notation "Stored" => SourceCurrentHereditaryNativeUniversalStore.Stored Plain
local notation "CodeFields" => SourceCurrentAllocatedNativeCodeFields.Fields
local notation "DomainKey" => IntersectionFlatMemoKeyDomain.DomainKey
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
variable {width : Nat} {source : InternedConstructorTemplates.State Symbol Guard}
variable {inventory : List DomainKey} {initial : Cache.State DomainKey}

/-- The exact completed trace retains causal stores and its local output contract. -/
theorem completed (facts : InternedNestedFacts.Facts source)
    (closed : SourceCurrentAllocatedRecursiveDomainCode.Closed source inventory) (fuel : Nat) :
    Preserves source inventory initial width fuel := by
  induction fuel using Nat.strongRecOn with
  | ind count ih =>
    intro A control before after value physicalPost post known physical fields certificate stored trace
    have admitted := SourceCurrentAllocatedRecursivePrefixControl.entered source inventory control before.native.machine physicalPost physical
    cases count with
    | zero =>
      cases trace
      exact ⟨known, .refl _, SourceEqualityConstraintMemoAllocation.grows_refl _, stored,
        SourceCurrentAllocatedRecursivePrefixControl.pure_result source inventory value before.native.machine physicalPost physical,
        SourceCurrentHereditaryNativeControl.pure_result Plain source value before.native.machine post certificate⟩
    | succ fuel =>
      cases trace with
      | cons _ _ resume middle _ _ _ inputs one tail =>
        have effects := SourceCurrentAllocatedRecursivePrefixState.yielded control resume before middle known inputs admitted fields one
        apply SourceCurrentHereditaryNativePhysicalInduction.Return.prepend effects.2.1 effects.2.2.2.1
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
          have middleStored : Stored middle := by
            refine ⟨?_, ?_⟩
            · rw [nativeSame]; exact stored.constructors
            · rw [nativeSame]; exact stored.native
          have bodyCertificate := SourceCurrentHereditaryNativeEffectsEdge.body_certified source request before middle body
            known.good stored.constructors data.2.2 certificate.1 certificate.2.1 certificate.2.2.1 pureBody
          apply SourceCurrentHereditaryNativePhysicalInduction.bind (fuel + 1) fuel ih (by omega)
            (.code body) next middle after value _ _ physicalPost post effects.1 bodyPhysical bodyFields
            (fun result => SourceCurrentAllocatedNativeCodeFields.fields_grows before.operations middle.operations
              (next result) (fields.2 result) effects.2.2.2.1) bodyCertificate middleStored ?_ ?_ tail
          · intro result final current growth resident
            exact SourceCurrentAllocatedRecursivePrefixControl.edge_next source inventory request next before.native.machine physicalPost
              physical result final.native.machine current.good.native.machine (effects.2.1.trans growth) current.semantic resident
          · intro result final current growth finalStored resultPost
            exact certificate.2.2.2 result final.native.machine current.good.native.machine (effects.2.1.trans growth)
              finalStored.constructors resultPost.1
              (SourceCurrentHereditaryNativeControl.edge_law Plain source request result resultPost.2)
        | code code =>
          cases code with
          | pure | fail => cases one
          | finishNode | finishEdge => cases certificate
          | work job next =>
            obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj one
            have nextPhysical := SourceCurrentAllocatedRecursivePrefixCode.work_next source inventory job next
              before.native.machine physicalPost physical known.semantic _ _ rfl
            have afterMu := certificate.1 before.native.machine.heap stored.constructors
            have afterStored : Stored {before with native := (advance before.native
                {before.native.machine with heap := (run job before.native.machine.heap).2})} := ⟨afterMu,
              fun other => SourceCurrentHereditaryNativeCache.advance_stored Plain other before.native _ (stored.native other)⟩
            exact ih fuel (by omega) (.code (next (run job before.native.machine.heap).1)) _ after value physicalPost post effects.1 nextPhysical.2.2.2 effects.2.2.2.2
              (certificate.2 _ _ rfl nextPhysical.1 nextPhysical.2.1 afterMu) afterStored tail
          | enter domain left right first second next =>
            obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj one
            have nextPhysical := SourceCurrentAllocatedRecursivePrefixCode.enter_next source inventory domain left right first second next
              before.native.machine physicalPost physical known.semantic
            have afterStored : Stored {before with native := (advance before.native
                {before.native.machine with domains := (SourceRecursiveIntersectionEnvironment.enter
                  before.native.machine.domains domain.key left right first second).2})} := ⟨stored.constructors,
              fun other => SourceCurrentHereditaryNativeCache.advance_stored Plain other before.native _ (stored.native other)⟩
            exact ih fuel (by omega) (.code (next (SourceRecursiveIntersectionEnvironment.enter
              before.native.machine.domains domain.key left right first second).1)) _ after value physicalPost post effects.1 nextPhysical.2.2.2 effects.2.2.2.2
              certificate.2.2 afterStored tail
          | read name next =>
            obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj one
            exact ih fuel (by omega) (.code (next (SourcePreparedSharedRows.read before.native.machine.heap name))) _ after value physicalPost post effects.1
              (SourceCurrentAllocatedRecursivePrefixCode.read_next source inventory name next before.native.machine physicalPost physical)
              effects.2.2.2.2 certificate stored tail
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
                have retained := SourceCurrentHereditaryNativeEffects.optionalBinder_result Plain pair body before.native.machine
                  known.good.native.machine stored.constructors certificate.1 certificate.2.1 _ _ done
                have afterStored : Stored {before with native := (advance before.native
                    {before.native.machine with heap := heap})} := ⟨retained.1,
                  fun other => SourceCurrentHereditaryNativeCache.advance_stored Plain other before.native _ (stored.native other)⟩
                exact ih fuel (by omega) (.code (next result)) _ after value physicalPost post effects.1 nextPhysical.2.2.2 effects.2.2.2.2
                  (certificate.2.2 _ _ done nextPhysical.1 nextPhysical.2.1 retained.1) afterStored tail
          | node request next =>
            have data := SourceCurrentAllocatedRecursivePrefixCode.node_data source inventory request next before.native.machine physicalPost physical
            have words := inputs.2
            obtain ⟨machine, operations, _nativeStored, branches⟩ := SourceCurrentHereditaryNativeTransition.node_yielded Plain source request next
              before resume middle known.good.native (stored.native source) data.1 words one
            have middleStored : Stored middle := SourceCurrentHereditaryNativeUniversalStore.node_yielded Plain source request next before middle resume known.good.native stored data.1 words one
            have ready : NodeReady middle.native.machine request := by rw [machine]; exact data.1
            have bodyPhysical := SourceCurrentAllocatedRecursivePrefixCode.node_certified source inventory facts closed
              request data.2.1 data.2.2 middle.native.machine effects.1.good.native.machine effects.1.semantic ready effects.1.growth effects.1.history
            have bodyCertificate := SourceCurrentHereditaryNativeEffectsCompile.node_certified Plain source request certificate.1
              data.2.1.leftAvailable data.2.1.rightAvailable certificate.2.1 certificate.2.2.1 middle.native.machine
              effects.1.good.native.machine middleStored.constructors ready effects.1.growth effects.1.history
            have bodyFields := SourceCurrentAllocatedNativeCodeFields.compileNode_fields middle.operations request
            have nextFields : ∀ result, CodeFields middle.operations (next result) := by rw [operations]; exact fields
            have continuation : ∀ result (final : Checked width), Current source inventory initial final →
                Extension middle.native.machine final.native.machine → Available final.native.machine.heap result →
                Physical source inventory (.code (next result)) final.native.machine physicalPost := by
              intro result final current growth available
              exact SourceCurrentAllocatedRecursivePrefixCode.node_next source inventory request next before.native.machine physicalPost
                physical result final.native.machine current.good.native.machine (effects.2.1.trans growth) current.semantic available
            have localNext : ∀ result (final : Checked width), Current source inventory initial final →
                Extension middle.native.machine final.native.machine → Stored final →
                (Available final.native.machine.heap result ∧ Annotated Plain result) →
                Certified source (.code (next result)) final.native.machine post := by
              intro result final current growth finalStored resultPost
              exact certificate.2.2.2 result final.native.machine current.good.native.machine (effects.2.1.trans growth)
                finalStored.constructors resultPost.1
                (SourceCurrentHereditaryNativeControl.node_law Plain source request result resultPost.2)
            rcases branches with ⟨rfl, _⟩ | ⟨result, rfl, available, law⟩ | ⟨handle, rfl, running⟩
            · exact SourceCurrentHereditaryNativePhysicalInduction.bind (fuel + 1) fuel ih (by omega)
                (.code (compileNode request)) next middle after value _ _ physicalPost post effects.1 bodyPhysical bodyFields nextFields
                bodyCertificate middleStored continuation localNext tail
            · exact ih fuel (by omega) _ middle after value physicalPost post effects.1
                (continuation result middle effects.1 (.refl _) available) (nextFields result)
                (certificate.2.2.2 result middle.native.machine effects.1.good.native.machine effects.2.1 middleStored.constructors available law)
                middleStored tail
            · exact SourceCurrentHereditaryNativePhysicalInduction.node_bind (fuel + 1) fuel handle ih (by omega)
                request next middle after value physicalPost post effects.1 bodyPhysical bodyFields nextFields
                bodyCertificate middleStored running continuation localNext tail
          | edge request next =>
            have data := SourceCurrentAllocatedRecursivePrefixCode.edge_data source inventory request next before.native.machine physicalPost physical
            have words := inputs.2
            obtain ⟨machine, operations, _nativeStored, branches⟩ := SourceCurrentHereditaryNativeTransition.edge_yielded Plain source request next
              before resume middle known.good.native (stored.native source) data.1 words one
            have middleStored : Stored middle := SourceCurrentHereditaryNativeUniversalStore.edge_yielded Plain source request next before middle resume known.good.native stored data.1 words one
            have ready : EdgeReady middle.native.machine request := by rw [machine]; exact data.1
            have bodyPhysical := SourceCurrentAllocatedRecursivePrefixControl.edge_body source inventory request
              middle.native.machine data.2.1 data.2.2 ready
            have bodyCertificate : Certified source (.edgeBody request .pure) middle.native.machine
                (fun final result => EdgeResident final.heap result ∧ SourceCurrentHereditaryConstructors.Edge Plain result) :=
              ⟨certificate.1, certificate.2.1, certificate.2.2.1,
                fun _ _ _ _ _ resident law => ⟨resident, law certificate.1 certificate.2.1 certificate.2.2.1⟩⟩
            have bodyFields : Fields (.edgeBody request .pure) middle := ⟨ready, fun _ => trivial⟩
            have nextFields : ∀ result, CodeFields middle.operations (next result) := by rw [operations]; exact fields
            have continuation : ∀ result (final : Checked width), Current source inventory initial final →
                Extension middle.native.machine final.native.machine → EdgeResident final.native.machine.heap result →
                Physical source inventory (.code (next result)) final.native.machine physicalPost := by
              intro result final current growth resident
              exact SourceCurrentAllocatedRecursivePrefixCode.edge_next source inventory request next before.native.machine physicalPost
                physical result final.native.machine current.good.native.machine (effects.2.1.trans growth) current.semantic resident
            have localNext : ∀ result (final : Checked width), Current source inventory initial final →
                Extension middle.native.machine final.native.machine → Stored final →
                (EdgeResident final.native.machine.heap result ∧ SourceCurrentHereditaryConstructors.Edge Plain result) →
                Certified source (.code (next result)) final.native.machine post := by
              intro result final current growth finalStored resultPost
              exact certificate.2.2.2 result final.native.machine current.good.native.machine (effects.2.1.trans growth)
                finalStored.constructors resultPost.1
                (SourceCurrentHereditaryNativeControl.edge_law Plain source request result resultPost.2)
            rcases branches with ⟨result, rfl, resident, law⟩ | ⟨handle, rfl, running⟩
            · exact ih fuel (by omega) _ middle after value physicalPost post effects.1
                (continuation result middle effects.1 (.refl _) resident) (nextFields result)
                (certificate.2.2.2 result middle.native.machine effects.1.good.native.machine effects.2.1 middleStored.constructors resident law)
                middleStored tail
            · exact SourceCurrentHereditaryNativePhysicalInduction.edge_bind (fuel + 1) fuel handle ih (by omega)
                request next middle after value physicalPost post effects.1 bodyPhysical bodyFields nextFields
                bodyCertificate middleStored running continuation localNext tail

end MicroCFTA.SourceCurrentHereditaryNativePhysicalTrace
