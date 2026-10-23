import MicroCFTA.SourceCurrentAllocatedRecursivePrefixInduction
import MicroCFTA.SourceCurrentAllocatedRecursiveRequestStep
import MicroCFTA.SourceEqualityNativeDemandBodyYield

/-!
# Recursive checked prefix admission from initial supplies

Strong induction follows the supplied raw prefix. Each demand derives its
current words from original operands and past domain allocation. Captured
finish frames receive their physical post from a shorter actual body trace.
-/
namespace MicroCFTA.SourceCurrentAllocatedRecursivePrefixAdmission
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand SourceCurrentAllocatedRecursivePrefixState
open SourceCurrentAllocatedNativeFieldClosure (Fields)
open SourceCurrentAllocatedRecursivePrefixReceipt (Receipt)
open SourceCurrentAllocatedRecursivePrefixInduction (Admits)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Certified" => SourceCurrentAllocatedRecursivePrefixControl.Certified
local notation "CodeFields" => SourceCurrentAllocatedNativeCodeFields.Fields
local notation "DomainKey" => IntersectionFlatMemoKeyDomain.DomainKey

/-- The resource conditions describe only the fixed source and initial domain supply. -/
structure Resources (bits : Nat) (source : InternedConstructorTemplates.State Symbol Guard)
    (inventory : List DomainKey) (initial : Cache.State DomainKey) : Prop where
  /-- Original operands have complete physical source records. -/
  facts : Facts source
  /-- The initial finite inventory is closed under actual original domain entry. -/
  closed : SourceCurrentAllocatedRecursiveDomainCode.Closed source inventory
  /-- The initial domain cache has canonical stored identities. -/
  valid : Cache.Valid initial
  /-- Original node identities fit the source key field. -/
  nodes : source.nodes.next < 2 ^ bits
  /-- Original edge identities fit the source row field. -/
  edges : source.edges.next ≤ 2 ^ (bits + 2)
  /-- The complete initial domain inventory fits the remaining identity supply. -/
  room : initial.next + inventory.length < 2 ^ (bits + 1)

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
variable {bits : Nat} {source : InternedConstructorTemplates.State Symbol Guard}
variable {inventory : List DomainKey} {initial : Cache.State DomainKey}

/-- Every actual recursive raw prefix derives its physical checks and current source facts. -/
theorem prefixes (resources : Resources bits source inventory initial) (fuel : Nat) :
    Admits source inventory initial (bits + 2) fuel := by
  induction fuel using Nat.strongRecOn with
  | ind count ih =>
    intro A control before remaining after post known certificate fields trace
    have inputs := SourceCurrentAllocatedRecursivePrefixControl.inputs source inventory bits resources.facts initial
      control before post known certificate resources.valid resources.nodes resources.edges resources.room
    have admitted := SourceCurrentAllocatedRecursivePrefixControl.entered source inventory control before.native.machine post certificate
    cases count with
    | zero =>
      obtain ⟨rfl, rfl⟩ := steps_zero _ _ _ _ trace
      apply SourceCurrentAllocatedRecursivePrefixReceipt.zero _ before known inputs admitted fields
      intro value same
      subst control
      exact SourceCurrentAllocatedRecursivePrefixControl.pure_result source inventory value before.native.machine post certificate
    | succ fuel =>
      obtain ⟨resume, middle, one, tail⟩ := steps_succ fuel _ _ _ _ trace
      have effects := SourceCurrentAllocatedRecursivePrefixState.yielded control resume before middle known inputs admitted fields one
      apply SourceCurrentAllocatedRecursivePrefixReceipt.before_step control resume before middle known inputs admitted fields one
      cases control with
      | edgeBody request next =>
        obtain ⟨body, pureBody, same⟩ := SourceEqualityNativeDemandBodyYield.yielded_unbind request next
          before middle resume one
        subst resume
        have data := SourceCurrentAllocatedRecursivePrefixControl.edge_data source inventory request next before.native.machine post certificate
        have bodyCertificate : Certified source inventory (.code body) middle.native.machine
            (fun final value => EdgeResident final.heap value) :=
          SourceCurrentAllocatedRecursivePrefixCode.body_certified source inventory resources.facts request data.1 data.2.1
            before middle body known.good.native.machine known.semantic data.2.2 pureBody
        have bodyFields := SourceCurrentAllocatedNativeFieldClosure.body_fields request .pure before middle (.code body)
          known.good.fields data.2.2 known.good.operations (fun _ => trivial) pureBody
        apply SourceCurrentAllocatedRecursivePrefixInduction.bind (fuel + 1) fuel ih (by omega)
          (.code body) next middle after remaining _ post effects.1 bodyCertificate bodyFields
          (fun value => SourceCurrentAllocatedNativeCodeFields.fields_grows before.operations middle.operations
            (next value) (fields.2 value) effects.2.2.2.1) ?_ tail
        intro value final current growth resident
        exact SourceCurrentAllocatedRecursivePrefixControl.edge_next source inventory request next before.native.machine post
          certificate value final.native.machine current.good.native.machine (effects.2.1.trans growth) current.semantic resident
      | code code =>
        cases code with
        | pure | fail => cases one
        | finishNode | finishEdge => cases certificate.safe
        | work job next =>
          obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj one
          have nextCertificate := SourceCurrentAllocatedRecursivePrefixCode.work_next source inventory job next
            before.native.machine post certificate known.semantic _ _ rfl
          exact ih fuel (by omega) _ _ remaining after post effects.1 nextCertificate.2.2.2 effects.2.2.2.2 tail
        | enter domain left right first second next =>
          obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj one
          have nextCertificate := SourceCurrentAllocatedRecursivePrefixCode.enter_next source inventory domain left right first second next
            before.native.machine post certificate known.semantic
          exact ih fuel (by omega) _ _ remaining after post effects.1 nextCertificate.2.2.2 effects.2.2.2.2 tail
        | read name next =>
          obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj one
          exact ih fuel (by omega) _ _ remaining after post effects.1
            (SourceCurrentAllocatedRecursivePrefixCode.read_next source inventory name next before.native.machine post certificate)
            effects.2.2.2.2 tail
        | optionalBinder pair value next =>
          cases actual : SourceRecursiveIntersectionMaybeMu.maybeMu pair value before.native.machine.heap with
          | pending key heap =>
            simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step, actual, lift] at one
            cases one
          | done result heap =>
            simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step, actual, lift] at one
            obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj one
            have done : construction (SourceRecursiveIntersectionMaybeMu.maybeMu pair value before.native.machine.heap)
                before.native.machine = .done result {before.native.machine with heap := heap} := by rw [actual]; rfl
            have nextCertificate := SourceCurrentAllocatedRecursivePrefixCode.optionalBinder_next source inventory pair value next
              before.native.machine post certificate known.semantic _ _ done
            exact ih fuel (by omega) _ _ remaining after post effects.1 nextCertificate.2.2.2 effects.2.2.2.2 tail
        | node request next =>
          have data := SourceCurrentAllocatedRecursivePrefixCode.node_data source inventory request next before.native.machine post certificate
          have words := SourceCurrentAllocatedRecursivePrefixControl.words source inventory bits resources.facts initial
            (.code (.node request next)) before post known certificate resources.valid resources.nodes resources.edges resources.room
          obtain ⟨machine, operations, branches⟩ := SourceCurrentAllocatedRecursiveRequestStep.node_yielded request next
            before resume middle known.good.native data.1 words one
          have ready : NodeReady middle.native.machine request := by rw [machine]; exact data.1
          have bodyCertificate := SourceCurrentAllocatedRecursivePrefixCode.node_certified source inventory
            resources.facts resources.closed request data.2.1 data.2.2 middle.native.machine
            effects.1.good.native.machine effects.1.semantic ready effects.1.growth effects.1.history
          have bodyFields := SourceCurrentAllocatedNativeCodeFields.compileNode_fields middle.operations request
          have nextFields : ∀ value, CodeFields middle.operations (next value) := by rw [operations]; exact fields
          have continuation : ∀ value (final : Checked (bits + 2)), Current source inventory initial final →
              Extension middle.native.machine final.native.machine → Available final.native.machine.heap value →
              Certified source inventory (.code (next value)) final.native.machine post := by
            intro value final current growth available
            exact SourceCurrentAllocatedRecursivePrefixCode.node_next source inventory request next before.native.machine post
              certificate value final.native.machine current.good.native.machine (effects.2.1.trans growth) current.semantic available
          rcases branches with ⟨rfl, _⟩ | ⟨value, rfl, available⟩ | ⟨handle, rfl, running⟩
          · exact SourceCurrentAllocatedRecursivePrefixInduction.bind (fuel + 1) fuel ih (by omega)
              (.code (compileNode request)) next middle after remaining _ post effects.1 bodyCertificate bodyFields nextFields continuation tail
          · exact ih fuel (by omega) _ middle remaining after post effects.1
              (continuation value middle effects.1 (.refl _) available) (nextFields value) tail
          · exact SourceCurrentAllocatedRecursivePrefixInduction.node_bind (fuel + 1) fuel handle ih (by omega)
              request next middle after remaining post effects.1 bodyCertificate bodyFields nextFields running continuation tail
        | edge request next =>
          have data := SourceCurrentAllocatedRecursivePrefixCode.edge_data source inventory request next before.native.machine post certificate
          have words := SourceCurrentAllocatedRecursivePrefixControl.words source inventory bits resources.facts initial
            (.code (.edge request next)) before post known certificate resources.valid resources.nodes resources.edges resources.room
          obtain ⟨machine, operations, branches⟩ := SourceCurrentAllocatedRecursiveRequestStep.edge_yielded request next
            before resume middle known.good.native data.1 words one
          have ready : EdgeReady middle.native.machine request := by rw [machine]; exact data.1
          have bodyCertificate := SourceCurrentAllocatedRecursivePrefixControl.edge_body source inventory request
            middle.native.machine data.2.1 data.2.2 ready
          have bodyFields : Fields (.edgeBody request .pure) middle := ⟨ready, fun _ => trivial⟩
          have nextFields : ∀ value, CodeFields middle.operations (next value) := by rw [operations]; exact fields
          have continuation : ∀ value (final : Checked (bits + 2)), Current source inventory initial final →
              Extension middle.native.machine final.native.machine → EdgeResident final.native.machine.heap value →
              Certified source inventory (.code (next value)) final.native.machine post := by
            intro value final current growth resident
            exact SourceCurrentAllocatedRecursivePrefixCode.edge_next source inventory request next before.native.machine post
              certificate value final.native.machine current.good.native.machine (effects.2.1.trans growth) current.semantic resident
          rcases branches with ⟨value, rfl, resident⟩ | ⟨handle, rfl, running⟩
          · exact ih fuel (by omega) _ middle remaining after post effects.1
              (continuation value middle effects.1 (.refl _) resident) (nextFields value) tail
          · exact SourceCurrentAllocatedRecursivePrefixInduction.edge_bind (fuel + 1) fuel handle ih (by omega)
              request next middle after remaining post effects.1 bodyCertificate bodyFields nextFields running continuation tail

end MicroCFTA.SourceCurrentAllocatedRecursivePrefixAdmission
