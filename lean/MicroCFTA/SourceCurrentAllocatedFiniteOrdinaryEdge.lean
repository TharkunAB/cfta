import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryCode
import MicroCFTA.SourceCurrentAllocatedNativePhysicalTraceCompletion

/-!
# Structural certificates for the current checked edge body

Accepted code traverses the literal ordered child zip. Each child result
uses its own request certificate. The final constructor retains domain
children and both original height bounds. Mismatch and rejection emit
the source singleton-Empty sentinel. Allocation changes only operations
before that code runs. These are local code certificates, not execution
or completion theorems.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryEdge
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentAllocatedFiniteOrdinaryStored (NodeCertificate EdgeCertificate)
open SourceCurrentAllocatedFiniteOrdinaryCode (NodeInputs EdgeInputs Certified certified_bind)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "NodeDomain" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "ChildrenDomain" => SourceCurrentAllocatedFiniteOrdinaryDomain.Children
local notation "Checked" => SourceEqualityNativeDemand.State
private def ChildBounds (pair : Node × Node) (value : Node) : Prop := NodeDomain value ∧
  MergedOrdinaryHeight.height value ≤ MergedOrdinaryHeight.height pair.1 ∧
  MergedOrdinaryHeight.height value ≤ MergedOrdinaryHeight.height pair.2

private theorem child_list {pairs : List (Node × Node)} {values : List Node} (firstBound secondBound : Nat)
    (actual : All₂ ChildBounds pairs values)
    (bounded : ∀ pair ∈ pairs, MergedOrdinaryHeight.height pair.1 ≤ firstBound ∧
      MergedOrdinaryHeight.height pair.2 ≤ secondBound) :
    ChildrenDomain values ∧ ∀ value ∈ values, MergedOrdinaryHeight.height value ≤ firstBound ∧
      MergedOrdinaryHeight.height value ≤ secondBound := by
  induction actual with
  | nil => exact ⟨.nil, fun _ absent => nomatch absent⟩
  | @cons pair value pairs values first rest ih =>
      obtain ⟨tailDomain, tailBounds⟩ := ih (fun pair member => bounded pair (List.mem_cons_of_mem _ member))
      refine ⟨.cons first.1 tailDomain, ?_⟩
      intro output member
      rcases List.mem_cons.mp member with same | later
      · subst output
        have bounds := bounded pair List.mem_cons_self
        exact ⟨Nat.le_trans first.2.1 bounds.1, Nat.le_trans first.2.2 bounds.2⟩
      · exact tailBounds output later

variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem walk_receipt (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (pairs : List (Node × Node)) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (semantic : SemanticReady state.heap)
    (inputs : ∀ pair ∈ pairs, NodeInputs ⟨domain, pair.1, pair.2⟩) :
    Certified (walk (fun pair : Node × Node => requestNode domain pair.1 pair.2) pairs) state
      (fun after values => All₂ ChildBounds pairs values ∧ ∀ value ∈ values, Available after.heap value) := by
  induction pairs generalizing state with
  | nil => exact ⟨.nil, fun _ absent => nomatch absent⟩
  | cons pair pairs ih =>
      change NodeInputs ⟨domain, pair.1, pair.2⟩ ∧ _
      refine ⟨inputs pair List.mem_cons_self, ?_⟩
      intro result middle middleValid _ middleSemantic available certificate
      have child := inputs pair List.mem_cons_self
      have bounds := certificate child.1 child.2.1 child.2.2
      apply certified_bind (walk (fun pair : Node × Node => requestNode domain pair.1 pair.2) pairs) _
        middle middleValid middleSemantic _ _
        (ih middle middleValid middleSemantic (fun pair member => inputs pair (List.mem_cons_of_mem _ member)))
      intro results after _ growth _ tail
      refine ⟨.cons bounds tail.1, ?_⟩
      intro value member
      rcases List.mem_cons.mp member with same | later
      · subst value
        exact growth.available result available
      · exact tail.2 value later

private theorem edge_work (request : EdgeRequest Symbol Guard) (symbol : Symbol) (guard : Guard)
    (values : List Node) (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (semantic : SemanticReady state.heap) (domain : ChildrenDomain values)
    (available : ∀ value ∈ values, Available state.heap value)
    (bounded : ∀ value ∈ values,
      MergedOrdinaryHeight.height value ≤ MergedOrdinaryHeight.edgeHeight request.left ∧
      MergedOrdinaryHeight.height value ≤ MergedOrdinaryHeight.edgeHeight request.right) :
    Certified (.work (makeEdge symbol guard values) .pure) state
      (fun after result => EdgeCertificate request result ∧ EdgeResident after.heap result) := by
  intro result after done _ _ _ _
  obtain ⟨rfl, rfl⟩ := work_done _ state result after done
  refine ⟨?_, (InternedNestedFacts.edge_verified symbol guard values state.heap valid.1 available).result _ _ rfl⟩
  intro _ _ _
  have facts := semantic.ready.semantic.1.normal.facts
  exact ⟨SourceCurrentAllocatedFiniteOrdinaryDomain.makeEdge symbol guard values state.heap facts.coherent
      facts.cached available domain,
    SourceCurrentAllocatedFiniteOrdinaryDomain.makeEdge_bound symbol guard values state.heap facts.coherent
      facts.cached available _ (fun value member => (bounded value member).1),
    SourceCurrentAllocatedFiniteOrdinaryDomain.makeEdge_bound symbol guard values state.heap facts.coherent
      facts.cached available _ (fun value member => (bounded value member).2)⟩

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
    have left := inputs.2.1.member pair.1 inside.1
    have right := inputs.2.2.member pair.2 inside.2
    exact ⟨inputs.1, left, right⟩
  have children := walk_receipt request.domain (request.left.children.zip request.right.children)
    state valid semantic calls
  unfold SourceEqualityNativeCheckedCode.children
  apply certified_bind _ _ state valid semantic _ _ children
  intro values after afterValid _ afterSemantic actual
  have bounds : ∀ pair ∈ request.left.children.zip request.right.children,
      MergedOrdinaryHeight.height pair.1 ≤ MergedOrdinaryHeight.edgeHeight request.left ∧
      MergedOrdinaryHeight.height pair.2 ≤ MergedOrdinaryHeight.edgeHeight request.right := by
    intro pair member
    have inside := List.of_mem_zip member
    exact ⟨SourceCurrentAllocatedFiniteOrdinaryDomain.child_le_edge request.left pair.1 inside.1,
      SourceCurrentAllocatedFiniteOrdinaryDomain.child_le_edge request.right pair.2 inside.2⟩
  obtain ⟨domain, bounded⟩ := child_list _ _ actual.1 bounds
  exact edge_work request request.left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined)
    values after afterValid afterSemantic domain actual.2 bounded

private theorem sentinel_receipt (request : EdgeRequest Symbol Guard) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (semantic : SemanticReady state.heap) :
    Certified (SourceEqualityNativeCheckedCode.sentinel request.left) state
      (fun after result => EdgeCertificate request result ∧ EdgeResident after.heap result) := by
  apply edge_work request request.left.entry.key.symbol SourceEqualityConstraintConstructors.top [.empty]
    state valid semantic (.cons .empty .nil)
  · intro value member
    simp only [List.mem_singleton] at member
    subst value
    exact empty_available _
  · intro value member
    simp only [List.mem_singleton] at member
    subst value
    exact ⟨Nat.zero_le _, Nat.zero_le _⟩

private theorem certificate_only (code : Code Symbol Guard Edge) (request : EdgeRequest Symbol Guard)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (semantic : SemanticReady state.heap)
    (actual : Certified code state (fun after result => EdgeCertificate request result ∧ EdgeResident after.heap result)) :
    Certified code state (fun _ result => EdgeCertificate request result) := by
  have bound := certified_bind code .pure state valid semantic _ (fun _ result => EdgeCertificate request result)
    actual (fun _ _ _ _ _ receipt => receipt.1)
  simpa only [SourceEqualityNativeDemand.code_bind_pure] using bound

/-- Literal zipped child requests derive the result domain and both height bounds without an arity premise. -/
theorem children_certified (request : EdgeRequest Symbol Guard) (inputs : EdgeInputs request)
    (combined : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (semantic : SemanticReady state.heap) :
    Certified (SourceEqualityNativeCheckedCode.children request.domain request.left request.right combined) state
      (fun _ result => EdgeCertificate request result) :=
  certificate_only _ request state valid semantic (children_receipt request inputs combined state valid semantic)

/-- The literal sentinel is finite ordinary and has zero height below either original edge. -/
theorem sentinel_certified (request : EdgeRequest Symbol Guard) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (semantic : SemanticReady state.heap) :
    Certified (SourceEqualityNativeCheckedCode.sentinel request.left) state
      (fun _ result => EdgeCertificate request result) :=
  certificate_only _ request state valid semantic (sentinel_receipt request state valid semantic)

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
    exact bindCode _ (sentinel_receipt request _ good.native.machine semantic)
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
          exact bindCode _ (sentinel_receipt request _ good.native.machine semantic)
        · simp only [SourceEqualityNativeDemand.sentinel] at yielded
          cases yielded
          exact bindCode _ (sentinel_receipt request _ good.native.machine semantic)
        · cases yielded
          exact bindCode _ (children_receipt request inputs _ _ good.native.machine semantic)

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryEdge
