import MicroCFTA.SourceCurrentAllocatedRecursivePrefixCode
import MicroCFTA.SourceCurrentAllocatedRecursivePrefixState
import MicroCFTA.SourceCurrentAllocatedRecursivePrefixWords

/-!
# Current control certificates for recursive checked prefixes

A code control retains its local compiler certificate. A demanded edge body
retains its exact original request and physical continuation. Current source
keys and past domain allocations derive local word and physical input checks.
This component assumes no future prefix admission or completed recursive call.
-/
namespace MicroCFTA.SourceCurrentAllocatedRecursivePrefixControl
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceEqualityRequiredSemanticCache (SemanticReady)
open IntersectionFlatMemoKeyDomain
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State

variable (source : InternedConstructorTemplates.State Symbol Guard) (inventory : List DomainKey)

/-- A control retains current physical operands and fixed-source request scope. -/
def Certified [DecidableEq (EdgeKey Symbol Guard)] (control : Control A)
    (state : Machine Symbol Guard) (post : Machine Symbol Guard → A → Prop) : Prop :=
  match control with
  | .code code => SourceCurrentAllocatedRecursivePrefixCode.Certified source inventory code state post
  | .edgeBody request next => EdgeScope source request ∧ request.domain.key ∈ inventory ∧ EdgeReady state request ∧
      ∀ value after, SourceRecursiveIntersectionKernel.Valid after → Extension state after → SemanticReady after.heap →
        EdgeResident after.heap value → SourceCurrentAllocatedRecursivePrefixCode.Certified source inventory (next value) after post

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- A local code certificate supplies the same control certificate. -/
theorem code (body : Code Symbol Guard A) (state : Machine Symbol Guard) (post : Machine Symbol Guard → A → Prop)
    (certificate : SourceCurrentAllocatedRecursivePrefixCode.Certified source inventory body state post) :
    Certified source inventory (.code body) state post := certificate

/-- A pure current control supplies the physical post at its exact returned machine. -/
theorem pure_result (value : A) (state : Machine Symbol Guard) (post : Machine Symbol Guard → A → Prop)
    (certificate : Certified source inventory (.code (.pure value)) state post) : post state value :=
  SourceCurrentAllocatedRecursivePrefixCode.pure_result source inventory value state post certificate

/-- The local source certificate derives exact current domain-entry admission. -/
theorem entered (control : Control A) (state : Machine Symbol Guard) (post : Machine Symbol Guard → A → Prop)
    (certificate : Certified source inventory control state post) :
    SourceCurrentAllocatedNativeDomainTrace.Entered inventory control := by
  cases control with
  | code body => exact SourceCurrentAllocatedRecursivePrefixCode.entered source inventory body state post certificate
  | edgeBody => trivial

/-- Initial source keys and past domain allocation derive the current word check. -/
theorem words (bits : Nat) (facts : Facts source) (initial : Cache.State DomainKey)
    (control : Control A) (before : Checked (bits + 2)) (post : Machine Symbol Guard → A → Prop)
    (current : SourceCurrentAllocatedRecursivePrefixState.Current source inventory initial before)
    (certificate : Certified source inventory control before.native.machine post)
    (valid : Cache.Valid initial) (nodes : source.nodes.next < 2 ^ bits)
    (edges : source.edges.next ≤ 2 ^ (bits + 2))
    (room : initial.next + inventory.length < 2 ^ (bits + 1)) :
    SourceCurrentAllocatedNativeRequestBounds.Words (bits + 2) control := by
  cases control with
  | edgeBody => trivial
  | code body =>
      cases body with
      | node request next =>
          exact SourceCurrentAllocatedRecursivePrefixWords.node_words bits source facts inventory initial before request next
            certificate.domain.1 certificate.safe.1.1 current.domains valid nodes room
      | edge request next =>
          exact SourceCurrentAllocatedRecursivePrefixWords.edge_words bits source facts inventory initial before request next
            certificate.domain.1 certificate.safe.1.1 current.domains valid edges room
      | pure | fail | work | enter | read | optionalBinder | finishNode | finishEdge => trivial

/-- Current words and physical operands derive only this instruction's input check. -/
theorem inputs [DecidableEq Symbol] (bits : Nat) (facts : Facts source) (initial : Cache.State DomainKey)
    (control : Control A) (before : Checked (bits + 2)) (post : Machine Symbol Guard → A → Prop)
    (current : SourceCurrentAllocatedRecursivePrefixState.Current source inventory initial before)
    (certificate : Certified source inventory control before.native.machine post)
    (valid : Cache.Valid initial) (nodes : source.nodes.next < 2 ^ bits)
    (edges : source.edges.next ≤ 2 ^ (bits + 2))
    (room : initial.next + inventory.length < 2 ^ (bits + 1)) :
    SourceCurrentAllocatedNativePhysicalExecution.Inputs control before := by
  cases control with
  | edgeBody => trivial
  | code body =>
      exact SourceCurrentAllocatedRecursivePrefixCode.current_inputs source inventory body before post certificate
        (words source inventory bits facts initial (.code body) before post current certificate valid nodes edges room)

/-- Original resident rows supply a demanded body's physical-return continuation. -/
theorem edge_body (request : EdgeRequest Symbol Guard) (state : Machine Symbol Guard)
    (scope : EdgeScope source request) (member : request.domain.key ∈ inventory) (ready : EdgeReady state request) :
    Certified source inventory (.edgeBody request .pure) state (fun after value => EdgeResident after.heap value) :=
  ⟨scope, member, ready, fun _ _ _ _ _ resident => ⟨resident, trivial, resident⟩⟩

/-- A demanded edge body retains the complete original request before execution. -/
theorem edge_data (request : EdgeRequest Symbol Guard) (next : EdgeValue Symbol Guard → Code Symbol Guard A)
    (state : Machine Symbol Guard) (post : Machine Symbol Guard → A → Prop)
    (certificate : Certified source inventory (.edgeBody request next) state post) :
    EdgeScope source request ∧ request.domain.key ∈ inventory ∧ EdgeReady state request :=
  ⟨certificate.1, certificate.2.1, certificate.2.2.1⟩

/-- A demanded body's continuation uses only its actual returned physical facts. -/
theorem edge_next (request : EdgeRequest Symbol Guard) (next : EdgeValue Symbol Guard → Code Symbol Guard A)
    (state : Machine Symbol Guard) (post : Machine Symbol Guard → A → Prop)
    (certificate : Certified source inventory (.edgeBody request next) state post)
    (value : EdgeValue Symbol Guard) (after : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid after) (growth : Extension state after)
    (semantic : SemanticReady after.heap) (resident : EdgeResident after.heap value) :
    SourceCurrentAllocatedRecursivePrefixCode.Certified source inventory (next value) after post :=
  certificate.2.2.2 value after valid growth semantic resident

/-- The supplied actual edge-body yield derives its emitted control certificate. -/
theorem body_code (facts : Facts source) (request : EdgeRequest Symbol Guard)
    (before after : Checked width) (body : Code Symbol Guard (EdgeValue Symbol Guard))
    (valid : SourceRecursiveIntersectionKernel.Valid before.native.machine)
    (semantic : SemanticReady before.native.machine.heap)
    (certificate : Certified source inventory (.edgeBody request .pure) before.native.machine
      (fun final value => EdgeResident final.heap value))
    (yielded : SourceEqualityNativeDemand.body request .pure before = .yielded (.code body) after) :
    Certified source inventory (.code body) after.native.machine (fun final value => EdgeResident final.heap value) :=
  SourceCurrentAllocatedRecursivePrefixCode.body_certified source inventory facts request certificate.1 certificate.2.1
    before after body valid semantic certificate.2.2.1 yielded

end MicroCFTA.SourceCurrentAllocatedRecursivePrefixControl
