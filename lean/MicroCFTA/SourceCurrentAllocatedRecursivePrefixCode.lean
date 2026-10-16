import MicroCFTA.SourceCurrentAllocatedRecursiveDomainCode
import MicroCFTA.SourceCurrentAllocatedNativeDomainTrace
import MicroCFTA.SourceCurrentAllocatedNativePhysicalExecution

/-!
# Local physical and source certificates for recursive checked prefixes

Physical safety and operands refer to the current machine. Original operand
scope refers to a fixed source heap. The domain certificate records exact
inventory keys. Actual primitive returns retain all three certificates.
Driver finish frames remain a separate part of the prefix proof.
-/
namespace MicroCFTA.SourceCurrentAllocatedRecursivePrefixCode
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityRequiredSemanticCache (SemanticReady)
open IntersectionFlatMemoKeyDomain
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State

variable (source : InternedConstructorTemplates.State Symbol Guard) (inventory : List DomainKey)

/-- Current physical checks and fixed-source domain scope use the same code and post. -/
structure Certified [DecidableEq (EdgeKey Symbol Guard)] (code : Code Symbol Guard A)
    (state : Machine Symbol Guard) (post : Machine Symbol Guard → A → Prop) : Prop where
  /-- Actual source work preserves validity, extension, and the physical post. -/
  safe : Safe code state post
  /-- Each primitive has its actual current available or resident operands. -/
  operands : SourceCurrentAllocatedNativeCodeProgress.Operands code state
  /-- Original requests and literal enter keys stay in the fixed source inventory. -/
  domain : SourceCurrentAllocatedRecursiveDomainCode.Certified source inventory code state post

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- A pure return supplies the specified physical post in its exact machine. -/
theorem pure_result (value : A) (state : Machine Symbol Guard) (post : Machine Symbol Guard → A → Prop)
    (certificate : Certified source inventory (.pure value) state post) : post state value := certificate.safe

/-- Current heap inputs follow from primitive operands without any word check. -/
theorem heap_inputs (code : Code Symbol Guard A) (before : Checked width)
    (post : Machine Symbol Guard → A → Prop)
    (certificate : Certified source inventory code before.native.machine post) :
    SourceEqualityNativeDemandHeap.Inputs (.code code) before :=
  SourceCurrentAllocatedNativeCodeProgress.current_heap_inputs code before certificate.operands

/-- Current words combine with physical operands at this instruction only. -/
theorem current_inputs [DecidableEq Symbol] (code : Code Symbol Guard A) (before : Checked width)
    (post : Machine Symbol Guard → A → Prop)
    (certificate : Certified source inventory code before.native.machine post)
    (words : SourceCurrentAllocatedNativeRequestBounds.Words width (.code code)) :
    SourceCurrentAllocatedNativePhysicalExecution.Inputs (.code code) before :=
  SourceCurrentAllocatedNativePhysicalExecution.code_inputs code before certificate.operands words

/-- The source certificate supplies the exact local enter admission. -/
theorem entered (code : Code Symbol Guard A) (state : Machine Symbol Guard)
    (post : Machine Symbol Guard → A → Prop) (certificate : Certified source inventory code state post) :
    SourceCurrentAllocatedNativeDomainTrace.Entered inventory (.code code) := by
  cases code <;> first | exact certificate.domain.1 | trivial

/-- A current node request retains its complete original scope and inventory key. -/
theorem node_data (request : NodeRequest Symbol Guard) (next : Value Symbol Guard → Code Symbol Guard A)
    (state : Machine Symbol Guard) (post : Machine Symbol Guard → A → Prop)
    (certificate : Certified source inventory (.node request next) state post) :
    NodeReady state request ∧ NodeScope source request ∧ request.domain.key ∈ inventory :=
  ⟨certificate.safe.1, certificate.domain.1, certificate.domain.2.1⟩

/-- A current edge request retains its complete ordered rows and inventory key. -/
theorem edge_data (request : EdgeRequest Symbol Guard) (next : EdgeValue Symbol Guard → Code Symbol Guard A)
    (state : Machine Symbol Guard) (post : Machine Symbol Guard → A → Prop)
    (certificate : Certified source inventory (.edge request next) state post) :
    EdgeReady state request ∧ EdgeScope source request ∧ request.domain.key ∈ inventory :=
  ⟨certificate.safe.1, certificate.domain.1, certificate.domain.2.1⟩

/-- Actual work derives its returned machine facts before its continuation is used. -/
theorem work_next (job : Work Symbol Guard B) (next : B → Code Symbol Guard A)
    (state : Machine Symbol Guard) (post : Machine Symbol Guard → A → Prop)
    (certificate : Certified source inventory (.work job next) state post)
    (semantic : SemanticReady state.heap) (value : B) (after : Machine Symbol Guard)
    (done : work job state = .done value after) :
    SourceRecursiveIntersectionKernel.Valid after ∧ Extension state after ∧ SemanticReady after.heap ∧
      Certified source inventory (next value) after post := by
  have valid : SourceRecursiveIntersectionKernel.Valid after := by
    simpa only [done, Result.state] using certificate.safe.1
  have growth : Extension state after := by
    simpa only [done, Result.state] using certificate.safe.2.1
  have afterSemantic : SemanticReady after.heap := by
    obtain ⟨rfl, rfl⟩ := work_done job state value after done
    exact SourceCurrentAllocatedNativeSemanticHeap.work_semantic job state.heap semantic certificate.operands.1
  exact ⟨valid, growth, afterSemantic, certificate.safe.2.2 value after done,
    certificate.operands.2 value after done,
    certificate.domain value after done valid growth afterSemantic⟩

/-- Entry retains exact current domain allocation and the literal next certificate. -/
theorem enter_next (domain : Interned DomainKey) (left right : Value Symbol Guard) (first second : Nat)
    (next : Interned DomainKey → Code Symbol Guard A) (state : Machine Symbol Guard)
    (post : Machine Symbol Guard → A → Prop)
    (certificate : Certified source inventory (.enter domain left right first second next) state post)
    (semantic : SemanticReady state.heap) :
    let actual := SourceRecursiveIntersectionEnvironment.enter state.domains domain.key left right first second
    let after : Machine Symbol Guard := {state with domains := actual.2}
    SourceRecursiveIntersectionKernel.Valid after ∧ Extension state after ∧ SemanticReady after.heap ∧
      Certified source inventory (next actual.1) after post :=
  ⟨certificate.safe.1, certificate.safe.2.1, semantic, certificate.safe.2.2,
    certificate.operands.2.2.2, certificate.domain.2.2.2⟩

/-- A literal current-heap read retains all local certificates at the same machine. -/
theorem read_next (name : Nat) (next : Option (Value Symbol Guard) → Code Symbol Guard A)
    (state : Machine Symbol Guard) (post : Machine Symbol Guard → A → Prop)
    (certificate : Certified source inventory (.read name next) state post) :
    Certified source inventory (next (SourcePreparedSharedRows.read state.heap name)) state post :=
  ⟨certificate.safe, certificate.operands, certificate.domain⟩

/-- Actual optional binding derives its returned physical facts without a completion assumption. -/
theorem optionalBinder_next (pair : Nat × Nat) (body : Value Symbol Guard)
    (next : Value Symbol Guard → Code Symbol Guard A) (state : Machine Symbol Guard)
    (post : Machine Symbol Guard → A → Prop)
    (certificate : Certified source inventory (.optionalBinder pair body next) state post)
    (semantic : SemanticReady state.heap) (value : Value Symbol Guard) (after : Machine Symbol Guard)
    (done : construction (SourceRecursiveIntersectionMaybeMu.maybeMu pair body state.heap) state = .done value after) :
    SourceRecursiveIntersectionKernel.Valid after ∧ Extension state after ∧ SemanticReady after.heap ∧
      Certified source inventory (next value) after post := by
  have valid : SourceRecursiveIntersectionKernel.Valid after := by
    simpa only [done, Result.state] using certificate.safe.1
  have growth : Extension state after := by
    simpa only [done, Result.state] using certificate.safe.2.1
  have afterSemantic : SemanticReady after.heap := by
    have retained := SourceCurrentAllocatedNativeSemanticHeap.optionalBinder_semantic pair body state.heap
      semantic certificate.operands.1
    cases actual : SourceRecursiveIntersectionMaybeMu.maybeMu pair body state.heap with
    | pending key heap => simp only [construction, actual] at done; cases done
    | done result heap =>
        simp only [construction, actual] at done
        cases done
        simpa only [actual, InternedNestedConstruction.Outcome.state] using retained
  exact ⟨valid, growth, afterSemantic, certificate.safe.2.2 value after done,
    certificate.operands.2 value after done,
    certificate.domain value after done valid growth afterSemantic⟩

/-- A node continuation needs only the actual returned physical facts. -/
theorem node_next (request : NodeRequest Symbol Guard) (next : Value Symbol Guard → Code Symbol Guard A)
    (state : Machine Symbol Guard) (post : Machine Symbol Guard → A → Prop)
    (certificate : Certified source inventory (.node request next) state post)
    (value : Value Symbol Guard) (after : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid after) (growth : Extension state after)
    (semantic : SemanticReady after.heap) (available : Available after.heap value) :
    Certified source inventory (next value) after post :=
  ⟨certificate.safe.2 value after valid growth available,
    certificate.operands.2 value after valid growth available,
    certificate.domain.2.2 value after valid growth semantic available⟩

/-- An edge continuation needs only the actual returned residency and machine facts. -/
theorem edge_next (request : EdgeRequest Symbol Guard) (next : EdgeValue Symbol Guard → Code Symbol Guard A)
    (state : Machine Symbol Guard) (post : Machine Symbol Guard → A → Prop)
    (certificate : Certified source inventory (.edge request next) state post)
    (value : EdgeValue Symbol Guard) (after : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid after) (growth : Extension state after)
    (semantic : SemanticReady after.heap) (resident : EdgeResident after.heap value) :
    Certified source inventory (next value) after post :=
  ⟨certificate.safe.2 value after valid growth resident,
    certificate.operands.2 value after valid growth resident,
    certificate.domain.2.2 value after valid growth semantic resident⟩

/-- Original node operands derive the full local request certificate. -/
theorem request_node (request : NodeRequest Symbol Guard) (state : Machine Symbol Guard)
    (ready : NodeReady state request) (scope : NodeScope source request) (member : request.domain.key ∈ inventory) :
    Certified source inventory (requestNode request.domain request.left request.right) state
      (fun after value => Available after.heap value) :=
  ⟨safe_requestNode request.domain request.left request.right state ready,
    ⟨ready, fun _ _ _ _ _ => trivial⟩,
    SourceCurrentAllocatedRecursiveDomainCode.requestNode_certified source inventory request state scope member⟩

/-- Original resident rows derive the full local edge request certificate. -/
theorem request_edge (request : EdgeRequest Symbol Guard) (state : Machine Symbol Guard)
    (ready : EdgeReady state request) (scope : EdgeScope source request) (member : request.domain.key ∈ inventory) :
    Certified source inventory (requestEdge request.domain request.left request.right) state
      (fun after value => EdgeResident after.heap value) :=
  ⟨safe_requestEdge request.domain request.left request.right state ready,
    ⟨ready, fun _ _ _ _ _ => trivial⟩,
    SourceCurrentAllocatedRecursiveDomainCode.requestEdge_certified source inventory request state scope member⟩

/-- Node compilation combines existing physical and original-domain compiler proofs. -/
theorem node_certified [DecidableEq Symbol]
    (facts : Facts source) (closed : SourceCurrentAllocatedRecursiveDomainCode.Closed source inventory)
    (request : NodeRequest Symbol Guard) (scope : NodeScope source request) (member : request.domain.key ∈ inventory)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (semantic : SemanticReady state.heap) (ready : NodeReady state request)
    (growth : Grows source state.heap) (history : Extends source.nodes.issued state.heap.nodes.issued) :
    Certified source inventory (compileNode request) state (fun after value => Available after.heap value) :=
  ⟨compileNode_safe request state valid ready,
    SourceCurrentAllocatedNativeCodeProgress.compileNode_operands request state valid ready,
    SourceCurrentAllocatedRecursiveDomainCode.node_certified source inventory facts closed request scope member
      state valid semantic ready growth history⟩

/-- An actual checked body yield derives all local certificates at its own returned machine. -/
theorem body_certified
    (facts : Facts source) (request : EdgeRequest Symbol Guard) (scope : EdgeScope source request)
    (member : request.domain.key ∈ inventory) (before after : Checked width)
    (code : Code Symbol Guard (EdgeValue Symbol Guard))
    (valid : SourceRecursiveIntersectionKernel.Valid before.native.machine)
    (semantic : SemanticReady before.native.machine.heap) (ready : EdgeReady before.native.machine request)
    (yielded : SourceEqualityNativeDemand.body request .pure before = .yielded (.code code) after) :
    Certified source inventory code after.native.machine (fun final value => EdgeResident final.heap value) := by
  classical
  have physical := SourceCurrentAllocatedNativeCodeProgress.body_certified request before after code valid ready yielded
  exact ⟨physical.1, physical.2,
    SourceCurrentAllocatedRecursiveDomainCode.body_certified source inventory facts request scope member
      before after code valid semantic ready yielded⟩

end MicroCFTA.SourceCurrentAllocatedRecursivePrefixCode
