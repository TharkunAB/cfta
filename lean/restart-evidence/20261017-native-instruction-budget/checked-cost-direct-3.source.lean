import MicroCFTA.SourceRecursiveIntersectionCompileInstructionCredit
import MicroCFTA.SourceEqualityNativeCheckedMass
import MicroCFTA.SourceCurrentAllocatedNativeRequestBounds

/-!
# Instruction credit for the actual checked edge-body choice

Accepted child code uses the original source zip and semantic child ranks.
Rejected code uses one sentinel constructor. The actual equality operation
prefix changes no native state and supplies the chosen code itself.
-/
namespace MicroCFTA.SourceEqualityNativeCheckedInstructionCredit
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionInputView
open SourceRecursiveIntersectionNative IntersectSchedule
open SourceRecursiveIntersectionInstructionProfile (budget sourceBranching)
open SourceRecursiveIntersectionInstructionCredit (At)
variable {Symbol Formula : Type}
section Generic
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]
variable {source : State Symbol (SourceSymbolicIndex.Constraint Formula)} {holds : (SourceSymbolicIndex.Constraint Formula) → Language.Term Symbol → Bool} {limit rank : Nat}

/-- The accepted code pays one whole call per original child pair and one edge constructor. -/
theorem children_at (domain : Interned DomainKey) (left right : EdgeValue Symbol (SourceSymbolicIndex.Constraint Formula))
    (combined : SourceEqualityConjoinAllocation.Constraint Formula)
    (state : Machine Symbol (SourceSymbolicIndex.Constraint Formula)) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (known : Domain state domain) (leftResident : EdgeResident state.heap left) (rightResident : EdgeResident state.heap right)
    (bounds : ∀ pair ∈ left.children.zip right.children, NodeBelow source holds rank ⟨domain, pair.1, pair.2⟩) :
    At source holds limit (SourceEqualityNativeCheckedCode.children domain left right combined) state
      ((left.children.zip right.children).length * budget limit (rank - 1) + 1)
      (fun after edge => EdgeResident after.heap edge) := by
  let input := fun (current : Machine Symbol (SourceSymbolicIndex.Constraint Formula)) (pair : Value Symbol (SourceSymbolicIndex.Constraint Formula) × Value Symbol (SourceSymbolicIndex.Constraint Formula)) =>
    Domain current domain ∧ Available current.heap pair.1 ∧ Available current.heap pair.2
  have walked := SourceRecursiveIntersectionInstructionCredit.walk
    (fun pair : Value Symbol (SourceSymbolicIndex.Constraint Formula) × Value Symbol (SourceSymbolicIndex.Constraint Formula) => requestNode domain pair.1 pair.2)
    (left.children.zip right.children) (budget limit (rank - 1)) input (fun after value => Available after.heap value)
    (by
      intro before after growth pair current
      exact ⟨current.1.grows domain growth, growth.available _ current.2.1, growth.available _ current.2.2⟩)
    available_stable (by
      intro pair member current _ inputs
      exact SourceRecursiveIntersectionInstructionCredit.request_node ⟨domain, pair.1, pair.2⟩ current _ inputs
        (SourceRecursiveIntersectionCompileInstructionCredit.node_charge _ (bounds pair member)))
    state valid (by
      intro pair member
      have inside := List.of_mem_zip member
      exact ⟨known, valid.1.cached.edges _ _ leftResident _ inside.1,
        valid.1.cached.edges _ _ rightResident _ inside.2⟩)
  exact SourceRecursiveIntersectionInstructionCredit.bind _ _ state _ 1 valid _ _ walked
    (fun values after afterValid _ outputs => SourceRecursiveIntersectionInstructionCredit.edge _ _ values after afterValid outputs.2)

/-- Sentinel construction consumes one instruction and introduces no child request. -/
theorem sentinel_at (left : EdgeValue Symbol (SourceSymbolicIndex.Constraint Formula)) (state : Machine Symbol (SourceSymbolicIndex.Constraint Formula))
    (valid : SourceRecursiveIntersectionKernel.Valid state) :
    At source holds limit (SourceEqualityNativeCheckedCode.sentinel left) state 1
      (fun after edge => EdgeResident after.heap edge) := by
  exact SourceRecursiveIntersectionInstructionCredit.edge _ _ [.empty] state valid (by
    intro value member
    cases List.mem_singleton.mp member
    exact empty_available _)

end Generic

section Current
local notation "SourceSymbol" => SourceObservations.Label FullSyntax.Formula
local notation "SourceGuard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State

/-- An actual checked body yield derives its complete emitted-code credit from the original source rank. -/
theorem body_at [DecidableEq SourceSymbol] [DecidableEq (EdgeKey SourceSymbol SourceGuard)]
    (source : State SourceSymbol SourceGuard) (facts : InternedNestedFacts.Facts source)
    (holds : SourceGuard → Language.Term SourceSymbol → Bool)
    (request : EdgeRequest SourceSymbol SourceGuard) (scope : EdgeScope source request)
    (complete : Completes (view source holds) (edgeSemantic holds request))
    (before after : Checked width) (code : Code SourceSymbol SourceGuard (EdgeValue SourceSymbol SourceGuard))
    (valid : SourceRecursiveIntersectionKernel.Valid before.native.machine) (ready : EdgeReady before.native.machine request)
    (yielded : SourceEqualityNativeDemand.body request .pure before = .yielded (.code code) after) :
    after.native = before.native ∧
      At source holds (sourceBranching source) code after.native.machine
        (1 + sourceBranching source * budget (sourceBranching source)
          (requiredFuel (view source holds) (edgeSemantic holds request) complete - 1))
        (fun final edge => EdgeResident final.heap edge) := by
  obtain ⟨same, choice⟩ := SourceEqualityNativeCheckedMass.body_choice request before after code yielded
  refine ⟨same, ?_⟩
  rw [same]
  rcases choice with rfl | ⟨combined, arity, rfl⟩
  · exact SourceRecursiveIntersectionInstructionCredit.mono _ _ (sentinel_at (source := source) (holds := holds) (limit := sourceBranching source) request.left before.native.machine valid) (by omega)
  · have bounds := fun pair member => SourceCurrentAllocatedNativeRequestBounds.child_below
      source facts holds request scope complete arity pair member
    have own := children_at (limit := sourceBranching source) request.domain request.left request.right combined before.native.machine valid
      ready.1 ready.2.1 ready.2.2 bounds
    apply SourceRecursiveIntersectionInstructionCredit.mono _ _ own
    have enough := Nat.mul_le_mul_right
      (budget (sourceBranching source) (requiredFuel (view source holds) (edgeSemantic holds request) complete - 1))
      (SourceRecursiveIntersectionInstructionProfile.edge_zip source facts request scope)
    omega
end Current
end MicroCFTA.SourceEqualityNativeCheckedInstructionCredit
