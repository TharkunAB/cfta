import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOutputCode
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOutputConstructors
import MicroCFTA.SourceCurrentAllocatedNativePhysicalTraceCompletion

/-!
# Output profiles for the current checked edge body

Accepted code retains each original child occurrence in the literal zip.
The child certificates bound all returned ordinary descendants.
Rejected code emits the actual singleton-Empty sentinel.
The result profile permits that one-child arity at an initial arity of zero.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOutputEdge
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentAllocatedFiniteOrdinaryOutputStored (NodeCertificate EdgeCertificate)
open SourceCurrentAllocatedFiniteOrdinaryOutputCode (NodeInputs EdgeInputs Certified certified_bind)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "NodeShape" => SourceCurrentAllocatedFiniteOrdinaryNativeProfile.NodeShape
local notation "EdgeShape" => SourceCurrentAllocatedFiniteOrdinaryNativeProfile.EdgeShape
local notation "ChildrenShape" => SourceCurrentAllocatedFiniteOrdinaryNativeProfile.ChildrenShape
local notation "Checked" => SourceEqualityNativeDemand.State

private theorem child_list
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (seen : domain.key.seen = [])
    (rows arity : Nat) {pairs : List (Node × Node)} {values : List Node}
    (actual : All₂ (fun pair value => NodeCertificate ⟨domain, pair.1, pair.2⟩ value) pairs values)
    (profiles : ∀ pair ∈ pairs, NodeShape rows arity pair.1 ∧ NodeShape rows arity pair.2) :
    ChildrenShape (rows * rows) (max arity 1) values := by
  induction actual with
  | nil => trivial
  | @cons pair value pairs values first rest ih =>
      have inputs := profiles pair List.mem_cons_self
      exact ⟨first seen rows arity inputs.1 inputs.2,
        ih (fun pair member => profiles pair (List.mem_cons_of_mem _ member))⟩

variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem walk_receipt (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (pairs : List (Node × Node)) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (semantic : SemanticReady state.heap)
    (inputs : ∀ pair ∈ pairs, NodeInputs ⟨domain, pair.1, pair.2⟩) :
    Certified (walk (fun pair : Node × Node => requestNode domain pair.1 pair.2) pairs) state
      (fun after values => All₂ (fun pair value => NodeCertificate ⟨domain, pair.1, pair.2⟩ value) pairs values ∧
        ∀ value ∈ values, Available after.heap value) := by
  induction pairs generalizing state with
  | nil => exact ⟨.nil, fun _ absent => nomatch absent⟩
  | cons pair pairs ih =>
      change NodeInputs ⟨domain, pair.1, pair.2⟩ ∧ _
      refine ⟨inputs pair List.mem_cons_self, ?_⟩
      intro result middle middleValid _ middleSemantic available certificate
      apply certified_bind (walk (fun pair : Node × Node => requestNode domain pair.1 pair.2) pairs) _
        middle middleValid middleSemantic _ _
        (ih middle middleValid middleSemantic (fun pair member => inputs pair (List.mem_cons_of_mem _ member)))
      intro results after _ growth _ tail
      refine ⟨.cons certificate tail.1, ?_⟩
      intro value member
      rcases List.mem_cons.mp member with same | later
      · subst value
        exact growth.available result available
      · exact tail.2 value later

private theorem edge_work (request : EdgeRequest Symbol Guard) (symbol : Symbol) (guard : Guard)
    (values : List Node) (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (available : ∀ value ∈ values, Available state.heap value)
    (shaped : ∀ rows arity, EdgeShape rows arity request.left → EdgeShape rows arity request.right →
      ChildrenShape (rows * rows) (max arity 1) values ∧ values.length ≤ max arity 1) :
    Certified (.work (makeEdge symbol guard values) .pure) state
      (fun after result => EdgeCertificate request result ∧ EdgeResident after.heap result) := by
  intro result after done _ _ _ _
  obtain ⟨rfl, rfl⟩ := work_done _ state result after done
  refine ⟨?_, (InternedNestedFacts.edge_verified symbol guard values state.heap valid.1 available).result _ _ rfl⟩
  intro _ rows arity leftShape rightShape
  have output := shaped rows arity leftShape rightShape
  exact SourceCurrentAllocatedFiniteOrdinaryOutputConstructors.makeEdge symbol guard values state.heap
    valid.1.coherent valid.1.cached available output.1 output.2

private theorem children_receipt (request : EdgeRequest Symbol Guard) (inputs : EdgeInputs request)
    (combined : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (semantic : SemanticReady state.heap) :
    Certified (SourceEqualityNativeCheckedCode.children request.domain request.left request.right combined) state
      (fun after result => EdgeCertificate request result ∧ EdgeResident after.heap result) := by
  have calls : ∀ pair ∈ request.left.children.zip request.right.children,
      NodeInputs ⟨request.domain, pair.1, pair.2⟩ := by
    intro pair member
    have inside := List.of_mem_zip member
    exact ⟨inputs.1, inputs.2.1.member pair.1 inside.1, inputs.2.2.member pair.2 inside.2⟩
  have children := walk_receipt request.domain (request.left.children.zip request.right.children)
    state valid semantic calls
  unfold SourceEqualityNativeCheckedCode.children
  apply certified_bind _ _ state valid semantic _ _ children
  intro values after afterValid _ _ actual
  apply edge_work request request.left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined)
    values after afterValid actual.2
  intro rows arity leftShape rightShape
  refine ⟨child_list request.domain inputs.1 rows arity actual.1 ?_, ?_⟩
  · intro pair member
    have inside := List.of_mem_zip member
    exact ⟨SourceCurrentAllocatedFiniteOrdinaryNativeProfile.ChildrenShape.member _
        (SourceCurrentAllocatedFiniteOrdinaryNativeProfile.EdgeShape.children _ leftShape) _ inside.1,
      SourceCurrentAllocatedFiniteOrdinaryNativeProfile.ChildrenShape.member _
        (SourceCurrentAllocatedFiniteOrdinaryNativeProfile.EdgeShape.children _ rightShape) _ inside.2⟩
  · rw [← actual.1.length_eq, List.length_zip]
    exact Nat.le_trans (Nat.min_le_left _ _) (Nat.le_trans
      (SourceCurrentAllocatedFiniteOrdinaryNativeProfile.EdgeShape.arity _ leftShape) (Nat.le_max_left _ _))

private theorem sentinel_receipt (request : EdgeRequest Symbol Guard) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) :
    Certified (SourceEqualityNativeCheckedCode.sentinel request.left) state
      (fun after result => EdgeCertificate request result ∧ EdgeResident after.heap result) := by
  apply edge_work request request.left.entry.key.symbol SourceEqualityConstraintConstructors.top [.empty]
    state valid
  · intro value member
    simp only [List.mem_singleton] at member
    subst value
    exact empty_available _
  · intro rows arity _ _
    exact ⟨⟨True.intro, True.intro⟩, Nat.le_max_right _ _⟩

private theorem certificate_only (code : Code Symbol Guard Edge) (request : EdgeRequest Symbol Guard)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (semantic : SemanticReady state.heap)
    (actual : Certified code state (fun after result => EdgeCertificate request result ∧ EdgeResident after.heap result)) :
    Certified code state (fun _ result => EdgeCertificate request result) := by
  have bound := certified_bind code .pure state valid semantic _ (fun _ result => EdgeCertificate request result)
    actual (fun _ _ _ _ _ receipt => receipt.1)
  simpa only [SourceEqualityNativeDemand.code_bind_pure] using bound

/-- Literal zipped child requests derive the complete output profile without an arity-equality premise. -/
theorem children_certified (request : EdgeRequest Symbol Guard) (inputs : EdgeInputs request)
    (combined : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (semantic : SemanticReady state.heap) :
    Certified (SourceEqualityNativeCheckedCode.children request.domain request.left request.right combined) state
      (fun _ result => EdgeCertificate request result) :=
  certificate_only _ request state valid semantic (children_receipt request inputs combined state valid semantic)

/-- The literal sentinel retains one Empty child and permits the maximum of the original arity and one. -/
theorem sentinel_certified (request : EdgeRequest Symbol Guard) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (semantic : SemanticReady state.heap) :
    Certified (SourceEqualityNativeCheckedCode.sentinel request.left) state
      (fun _ result => EdgeCertificate request result) :=
  certificate_only _ request state valid semantic (sentinel_receipt request state valid)

omit [DecidableEq (EdgeKey Symbol Guard)] in
/-- Every yielded checked body emits code at its actual returned operation state. -/
theorem body_yielded_code {width : Nat} {Output : Type}
    (request : EdgeRequest Symbol Guard) (next : Edge → Code Symbol Guard Output)
    (before after : Checked width) (rest : SourceEqualityNativeDemand.Control Output)
    (yielded : SourceEqualityNativeDemand.body request next before = .yielded rest after) :
    ∃ code, rest = .code code := by
  unfold SourceEqualityNativeDemand.body at yielded
  split at yielded
  · simp only [SourceEqualityNativeDemand.sentinel] at yielded
    cases yielded
    exact ⟨_, rfl⟩
  · split at yielded
    · cases yielded
    · cases yielded
    · split at yielded
      · cases yielded
      · cases yielded
      · dsimp only at yielded
        split at yielded
        · cases yielded
        · simp only [SourceEqualityNativeDemand.sentinel] at yielded
          cases yielded
          exact ⟨_, rfl⟩
        · simp only [SourceEqualityNativeDemand.sentinel] at yielded
          cases yielded
          exact ⟨_, rfl⟩
        · cases yielded
          exact ⟨_, rfl⟩

/-- An actual checked body yield certifies its exact code before the enclosing driver finish. -/
theorem body_certified {width : Nat} {Output : Type}
    (request : EdgeRequest Symbol Guard) (inputs : EdgeInputs request)
    (before after : Checked width) (next : Edge → Code Symbol Guard Output) (rest : Code Symbol Guard Output)
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good before)
    (semantic : SemanticReady before.native.machine.heap)
    (yielded : SourceEqualityNativeDemand.body request next before = .yielded (.code rest) after)
    (post : Machine Symbol Guard → Output → Prop)
    (continuation : ∀ result final, SourceRecursiveIntersectionKernel.Valid final →
      Extension before.native.machine final → SemanticReady final.heap → EdgeResident final.heap result →
      EdgeCertificate request result → Certified (next result) final post) :
    Certified rest after.native.machine post := by
  have same : after.native = before.native := by
    simpa only [yielded, SourceEqualityNativeDemand.Outcome.state] using
      SourceEqualityNativeDemandOperations.body_native request next before
  rw [same]
  have bindCode : ∀ code, Certified code before.native.machine
      (fun final result => EdgeCertificate request result ∧ EdgeResident final.heap result) →
      Certified (code.bind next) before.native.machine post := by
    intro code certificate
    exact certified_bind code next before.native.machine good.native.machine semantic _ post certificate
      (fun result final valid growth ready receipt => continuation result final valid growth ready receipt.2 receipt.1)
  unfold SourceEqualityNativeDemand.body at yielded
  split at yielded
  · simp only [SourceEqualityNativeDemand.sentinel] at yielded
    cases yielded
    exact bindCode _ (sentinel_receipt request _ good.native.machine)
  · split at yielded
    · cases yielded
    · cases yielded
    · split at yielded
      · cases yielded
      · cases yielded
      · dsimp only at yielded
        split at yielded
        · cases yielded
        · simp only [SourceEqualityNativeDemand.sentinel] at yielded
          cases yielded
          exact bindCode _ (sentinel_receipt request _ good.native.machine)
        · simp only [SourceEqualityNativeDemand.sentinel] at yielded
          cases yielded
          exact bindCode _ (sentinel_receipt request _ good.native.machine)
        · cases yielded
          exact bindCode _ (children_receipt request inputs _ _ good.native.machine semantic)

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOutputEdge
