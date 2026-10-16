import MicroCFTA.SourceCurrentAllocatedNativeAdmissionCode
import MicroCFTA.SourceCurrentAllocatedNativeRequestAdmission
import MicroCFTA.SourceCurrentAllocatedNativeCodeProgress

/-!
# Admission certificates for actual checked edge bodies

The original row scope and child admission certify each ordered child
request. Returned child availability supplies the actual edge constructor.
A stopped branch constructs its sentinel without any recursive request.
The body receipt selects the emitted code and its exact returned machine.
No result language or future query completion supplies these certificates.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeAdmissionEdgeCertificates
open Cache Language IntersectSchedule InternedConstructorTemplates InternedProbeProvenance
open InternedNestedFacts InternedNestedProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView SourceCurrentAllocatedNativeAdmissionCache
open SourceCurrentAllocatedNativeAdmissionCode
open SourceEqualityRequiredSemanticCache (SemanticReady)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State

private theorem edge_work_certified [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (holds : Guard → Term Symbol → Bool)
    (inputs : FiniteInput (view source holds)) (symbol : Symbol) (guard : Guard)
    (values : List (Value Symbol Guard)) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (available : Values state.heap values) :
    Certified source holds inputs (.work (makeEdge symbol guard values) .pure) state
      (fun after value => EdgeResident after.heap value) := by
  intro value after done _ _ _
  obtain ⟨rfl, rfl⟩ := work_done _ state value after done
  exact (InternedNestedFacts.edge_verified symbol guard values state.heap valid.1 available).result _ _ rfl

/-- Accepted child code derives admission of every actual ordered child request. -/
theorem children_certified [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (holds : Guard → Term Symbol → Bool) (inputs : FiniteInput (view source holds))
    (request : EdgeRequest Symbol Guard) (scope : EdgeScope source request) (known : EdgeCovered inputs request)
    (combined : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (semantic : SemanticReady state.heap) (ready : EdgeReady state request) :
    Certified source holds inputs
      (SourceEqualityNativeCheckedCode.children request.domain request.left request.right combined) state
      (fun after value => EdgeResident after.heap value) := by
  let physical := fun (current : Machine Symbol Guard) (pair : Value Symbol Guard × Value Symbol Guard) =>
    Domain current request.domain ∧ Available current.heap pair.1 ∧ Available current.heap pair.2
  have stable : Stable physical := by
    intro before after growth pair resident
    exact ⟨resident.1.grows _ growth, growth.available _ resident.2.1, growth.available _ resident.2.2⟩
  have reached : ∀ pair ∈ request.left.children.zip request.right.children, physical state pair := by
    intro pair member
    have inside := List.of_mem_zip member
    exact ⟨ready.1, valid.1.cached.edges request.left.entry.key request.left ready.2.1 pair.1 inside.1,
      valid.1.cached.edges request.right.entry.key request.right ready.2.2 pair.2 inside.2⟩
  have children := walk_certified source holds inputs
    (fun pair : Value Symbol Guard × Value Symbol Guard => requestNode request.domain pair.1 pair.2)
    (request.left.children.zip request.right.children) physical (fun after value => Available after.heap value)
    stable available_stable (by
      intro pair member current _ _ _
      obtain ⟨childScope, childInputs⟩ := SourceCurrentAllocatedNativeRequestAdmission.child
        source facts holds (finiteInputMeaning (view source holds) inputs) request scope known.1 pair member
      exact requestNode_certified source holds inputs ⟨request.domain, pair.1, pair.2⟩ current
        childScope ⟨childInputs, known.2⟩) state valid semantic reached
  unfold SourceEqualityNativeCheckedCode.children
  apply certified_bind source holds inputs _ _ state valid semantic _ _ children
  intro values after afterValid _ _ available
  exact edge_work_certified source holds inputs request.left.entry.key.symbol
    (SourceEqualityConjoinAllocation.readback combined) values after afterValid available

/-- The literal stopped sentinel has no recursive request to admit. -/
theorem sentinel_certified [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (holds : Guard → Term Symbol → Bool)
    (inputs : FiniteInput (view source holds)) (left : EdgeValue Symbol Guard)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state) :
    Certified source holds inputs (SourceEqualityNativeCheckedCode.sentinel left) state
      (fun after value => EdgeResident after.heap value) := by
  apply edge_work_certified source holds inputs left.entry.key.symbol SourceEqualityConstraintConstructors.top
    [.empty] state valid
  intro value member
  simp only [List.mem_singleton] at member
  subst value
  exact empty_available _

/-- An actual checked body yield certifies only its literal emitted code and returned machine. -/
theorem body_certified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (holds : Guard → Term Symbol → Bool) (inputs : FiniteInput (view source holds))
    (request : EdgeRequest Symbol Guard) (scope : EdgeScope source request) (known : EdgeCovered inputs request)
    (before after : Checked width) (code : Code Symbol Guard (EdgeValue Symbol Guard))
    (valid : SourceRecursiveIntersectionKernel.Valid before.native.machine)
    (semantic : SemanticReady before.native.machine.heap) (ready : EdgeReady before.native.machine request)
    (yielded : SourceEqualityNativeDemand.body request .pure before = .yielded (.code code) after) :
    Certified source holds inputs code after.native.machine (fun final value => EdgeResident final.heap value) := by
  have same : after.native = before.native := by
    simpa only [yielded, SourceEqualityNativeDemand.Outcome.state] using
      SourceEqualityNativeDemandOperations.body_native request .pure before
  rw [same]
  unfold SourceEqualityNativeDemand.body at yielded
  split at yielded
  · simp only [SourceEqualityNativeDemand.sentinel, SourceEqualityNativeDemand.code_bind_pure] at yielded
    cases yielded
    exact sentinel_certified source holds inputs _ _ valid
  · split at yielded
    · cases yielded
    · cases yielded
    · split at yielded
      · cases yielded
      · cases yielded
      · dsimp only at yielded
        split at yielded
        · cases yielded
        · simp only [SourceEqualityNativeDemand.sentinel, SourceEqualityNativeDemand.code_bind_pure] at yielded
          cases yielded
          exact sentinel_certified source holds inputs _ _ valid
        · simp only [SourceEqualityNativeDemand.sentinel, SourceEqualityNativeDemand.code_bind_pure] at yielded
          cases yielded
          exact sentinel_certified source holds inputs _ _ valid
        · simp only [SourceEqualityNativeDemand.code_bind_pure] at yielded
          cases yielded
          exact children_certified source facts holds inputs request scope known _ _ valid semantic ready

end MicroCFTA.SourceCurrentAllocatedNativeAdmissionEdgeCertificates
