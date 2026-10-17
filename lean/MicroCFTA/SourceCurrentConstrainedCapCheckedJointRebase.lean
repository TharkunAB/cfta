import MicroCFTA.SourceCurrentConstrainedCapCheckedJointOrigins
import MicroCFTA.SourceCurrentConstrainedCapSourceWeightTransport

/-!
# Joint native laws at a later growing source

Captured origins recover old input and binding witnesses. Actual source
reads retain every scoped occurrence weight. Physical returned records
supply the availability needed for deep-name readback. No result law is
inferred from a vacuous old conditional store without captured origins.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapCheckedJointRebase
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceCurrentConstrainedCapCheckedJointOrigins (Seen NodeOrigin EdgeOrigin)
open SourceCurrentConstrainedCapCheckedJointCode (NodeLaw EdgeLaw)
local notation "Origins" => SourceCurrentConstrainedCapCheckedJointOrigins.Stored
local notation "Joint" => SourceCurrentConstrainedCapCheckedJointCache.Stored
local notation "Native" => SourceRecursiveIntersectionThunks.State
variable {width : Nat} {Symbol Guard : Type}

/-- Original pair-read origins supply the exact earlier weight support. -/
theorem seen_supported {source : State Symbol Guard} {domain : IntersectionFlatMemoKeyDomain.DomainKey}
    (seen : Seen source domain) : SourceCurrentConstrainedCapSourceWeightTransport.Supported source domain.seen := by
  intro pair member
  obtain ⟨left, right, _leftOriginal, _rightOriginal, first, second⟩ := seen pair member
  exact ⟨left, right, first, second⟩

/-- The same complete original pair records remain captured after source growth. -/
theorem seen_grows {source later : State Symbol Guard} {domain : IntersectionFlatMemoKeyDomain.DomainKey}
    (seen : Seen source domain) (growth : Grows source later)
    (history : Extends source.nodes.issued later.nodes.issued) : Seen later domain := by
  intro pair member
  obtain ⟨left, right, leftOriginal, rightOriginal, first, second⟩ := seen pair member
  exact ⟨left, right, leftOriginal, rightOriginal,
    SourceCurrentConstrainedCapSourceWeightTransport.read_grows source later growth history _ _ first,
    SourceCurrentConstrainedCapSourceWeightTransport.read_grows source later growth history _ _ second⟩

/-- A captured node retains its complete original scope in a larger source. -/
theorem node_origin {source later : State Symbol Guard} {request : NodeRequest Symbol Guard}
    (origin : NodeOrigin source request) (growth : Grows source later)
    (history : Extends source.nodes.issued later.nodes.issued) : NodeOrigin later request := by
  refine ⟨⟨origin.scope.left, origin.scope.right,
    origin.scope.leftAvailable.grows source later growth history,
    origin.scope.rightAvailable.grows source later growth history, ?_⟩,
    seen_grows origin.seen growth history⟩
  intro name member
  exact (origin.scope.bindings name member).grows source later growth history _

/-- A captured row retains its complete original resident rows in a larger source. -/
theorem edge_origin {source later : State Symbol Guard} {request : EdgeRequest Symbol Guard}
    (origin : EdgeOrigin source request) (growth : Grows source later)
    (history : Extends source.nodes.issued later.nodes.issued) : EdgeOrigin later request := by
  refine ⟨⟨edge_grows source later growth _ origin.scope.leftResident,
    edge_grows source later growth _ origin.scope.rightResident, origin.scope.left, origin.scope.right, ?_⟩,
    seen_grows origin.seen growth history⟩
  intro name member
  exact (origin.scope.bindings name member).grows source later growth history _

/-- Every actual captured cell retains its original witnesses in the larger source. -/
theorem origins {source later : State Symbol Guard} (state : Native width Symbol Guard)
    (growth : Grows source later) (history : Extends source.nodes.issued later.nodes.issued)
    (known : Origins source state) : Origins later state :=
  ⟨fun handle cell found => node_origin (known.nodes handle cell found) growth history,
    fun handle cell found => edge_origin (known.edges handle cell found) growth history⟩

/-- A captured node law derives its later conditional result law from actual old witnesses. -/
theorem node_law (annotation : Guard → Prop) (source later : State Symbol Guard)
    (growth : Grows source later) (history : Extends source.nodes.issued later.nodes.issued)
    (facts : Facts later) (request : NodeRequest Symbol Guard) (result : Value Symbol Guard)
    (origin : NodeOrigin source request) (available : Available later result)
    (known : NodeLaw annotation source request result) : NodeLaw annotation later request result := by
  intro depth bindings inputs left right
  have oldBindings := SourceCurrentConstrainedCapCheckedJointOrigins.bindings_back annotation source later
    growth history facts request.domain.key origin.scope.bindings bindings
  have old := known depth oldBindings (origin.inputs_back inputs) left right
  exact ⟨old.1, SourceCurrentConstrainedCapSourceWeightTransport.classified annotation source later growth history
    request.domain.key.seen (seen_supported origin.seen) result facts.coherent available old.2.2 _ old.2.1, old.2.2⟩

/-- A captured row law retains its exact child budget and pair scope in the later source. -/
theorem edge_law (annotation : Guard → Prop) (source later : State Symbol Guard)
    (growth : Grows source later) (history : Extends source.nodes.issued later.nodes.issued)
    (sourceFacts : Facts source) (laterFacts : Facts later)
    (request : EdgeRequest Symbol Guard) (result : EdgeValue Symbol Guard) (origin : EdgeOrigin source request)
    (known : EdgeLaw annotation source request result) : EdgeLaw annotation later request result := by
  intro depth bindings inputs left right
  have oldBindings := SourceCurrentConstrainedCapCheckedJointOrigins.bindings_back annotation source later
    growth history laterFacts request.domain.key origin.scope.bindings bindings
  have old := known depth oldBindings (origin.inputs_back sourceFacts inputs) left right
  refine ⟨old.1, ?_, old.2.2⟩
  intro child member
  exact SourceCurrentConstrainedCapSourceWeightTransport.free_le annotation source later growth history
    request.domain.key.seen (seen_supported origin.seen) child (old.2.2 child member) _ (old.2.1 child member)

/-- Actual captured origins and physical returned records rebase both joint memo families together. -/
theorem rebase (annotation : Guard → Prop) (source : State Symbol Guard) (state : Native width Symbol Guard)
    (sourceFacts : Facts source) (growth : Grows source state.machine.heap)
    (history : Extends source.nodes.issued state.machine.heap.nodes.issued)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid state)
    (captured : Origins source state) (known : Joint annotation source state) :
    Joint annotation state.machine.heap state ∧ Origins state.machine.heap state := by
  refine ⟨⟨?_, ?_⟩, origins state growth history captured⟩
  · intro handle request result found
    exact node_law annotation source state.machine.heap growth history physical.machine.1 request result
      (captured.nodes handle ⟨request, .returned result⟩ found)
      (physical.nodes.checked handle ⟨request, .returned result⟩ found).2 (known.nodes handle request result found)
  · intro handle request result found
    exact edge_law annotation source state.machine.heap growth history sourceFacts physical.machine.1 request result
      (captured.edges handle ⟨request, .returned result⟩ found) (known.edges handle request result found)

end MicroCFTA.SourceCurrentConstrainedCapCheckedJointRebase
