import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryEdge

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.funBinderTypes true

#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryEdge.children_certified
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryEdge.children_certified
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryEdge.sentinel_certified
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryEdge.sentinel_certified
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryEdge.body_yielded_code
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryEdge.body_yielded_code
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryEdge.body_certified
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryEdge.body_certified

namespace FiniteOrdinaryEdgeChecks
open MicroCFTA Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentAllocatedFiniteOrdinaryStored (EdgeCertificate)
open SourceCurrentAllocatedFiniteOrdinaryCode (EdgeInputs Certified)
open SourceCurrentAllocatedFiniteOrdinaryEdge
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "Edge" => EdgeValue Symbol Guard
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
variable [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

theorem yielded_body_derives_its_local_certificate
    (request : EdgeRequest Symbol Guard) (inputs : EdgeInputs request)
    (before after : Checked width) (rest : SourceEqualityNativeDemand.Control Edge)
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good before)
    (semantic : SemanticReady before.native.machine.heap)
    (yielded : SourceEqualityNativeDemand.body request .pure before = .yielded rest after) :
    ∃ code, rest = .code code ∧ Certified code after.native.machine (fun _ result => EdgeCertificate request result) := by
  obtain ⟨code, rfl⟩ := body_yielded_code request .pure before after rest yielded
  refine ⟨code, rfl, ?_⟩
  exact body_certified request inputs before after .pure code good semantic yielded _
    (fun _ _ _ _ _ _ certificate => certificate)

theorem mismatch_skips_fields_and_children_at_literal_operations
    (request : EdgeRequest Symbol Guard) (before : Checked width)
    (valid : SourceRecursiveIntersectionKernel.Valid before.native.machine)
    (semantic : SemanticReady before.native.machine.heap)
    (mismatch : request.left.children.length ≠ request.right.children.length) :
    let code := SourceEqualityNativeCheckedCode.sentinel request.left
    let after : Checked width := {before with operations := SourceEqualityMkEdgeAllocation.emptyField before.operations}
    SourceEqualityNativeDemand.body request .pure before = .yielded (.code code) after ∧
      after.native = before.native ∧ Certified code after.native.machine (fun _ result => EdgeCertificate request result) := by
  refine ⟨?_, rfl, sentinel_certified request _ valid semantic⟩
  simpa only [SourceEqualityNativeDemand.sentinel, SourceEqualityNativeDemand.code_bind_pure] using
    SourceEqualityNativeDemand.body_mismatch request (.pure : Edge → Code Symbol Guard Edge) before mismatch

theorem rejected_conjunction_retains_allocation_and_emits_certified_sentinel
    (request : EdgeRequest Symbol Guard) (before : Checked width) (first second : Allocated)
    (valid : SourceRecursiveIntersectionKernel.Valid before.native.machine)
    (semantic : SemanticReady before.native.machine.heap)
    (arity : request.left.children.length = request.right.children.length)
    (left : SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint before.operations.constraints = .ok (some first))
    (right : SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint before.operations.constraints = .ok (some second))
    (rejected : (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
      request.left.children.length request.right.children.length before.operations).1 = .ok .rejected) :
    let checked := SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
      request.left.children.length request.right.children.length before.operations
    let after : Checked width := {before with operations := SourceEqualityMkEdgeAllocation.emptyField checked.2}
    let code := SourceEqualityNativeCheckedCode.sentinel request.left
    SourceEqualityNativeDemand.body request .pure before = .yielded (.code code) after ∧
      after.native = before.native ∧ Certified code after.native.machine (fun _ result => EdgeCertificate request result) := by
  refine ⟨?_, rfl, sentinel_certified request _ valid semantic⟩
  simpa only [SourceEqualityNativeDemand.sentinel, SourceEqualityNativeDemand.code_bind_pure] using
    SourceEqualityNativeDemand.body_rejected request (.pure : Edge → Code Symbol Guard Edge)
      before arity first second left right rejected

theorem accepted_conjunction_uses_actual_combined_and_zipped_requests
    (request : EdgeRequest Symbol Guard) (inputs : EdgeInputs request)
    (before : Checked width) (first second combined : Allocated)
    (valid : SourceRecursiveIntersectionKernel.Valid before.native.machine)
    (semantic : SemanticReady before.native.machine.heap)
    (arity : request.left.children.length = request.right.children.length)
    (left : SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint before.operations.constraints = .ok (some first))
    (right : SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint before.operations.constraints = .ok (some second))
    (ready : (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
      request.left.children.length request.right.children.length before.operations).1 = .ok (.ready combined)) :
    let checked := SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
      request.left.children.length request.right.children.length before.operations
    let after : Checked width := {before with operations := checked.2}
    let code := SourceEqualityNativeCheckedCode.children request.domain request.left request.right combined
    SourceEqualityNativeDemand.body request .pure before = .yielded (.code code) after ∧
      after.native = before.native ∧ Certified code after.native.machine (fun _ result => EdgeCertificate request result) := by
  refine ⟨?_, rfl, children_certified request inputs combined _ valid semantic⟩
  simpa only [SourceEqualityNativeDemand.code_bind_pure] using
    SourceEqualityNativeDemand.body_ready request (.pure : Edge → Code Symbol Guard Edge)
      before arity first second combined left right ready

end FiniteOrdinaryEdgeChecks

#print axioms FiniteOrdinaryEdgeChecks.yielded_body_derives_its_local_certificate
#check @FiniteOrdinaryEdgeChecks.yielded_body_derives_its_local_certificate
#print axioms FiniteOrdinaryEdgeChecks.mismatch_skips_fields_and_children_at_literal_operations
#check @FiniteOrdinaryEdgeChecks.mismatch_skips_fields_and_children_at_literal_operations
#print axioms FiniteOrdinaryEdgeChecks.rejected_conjunction_retains_allocation_and_emits_certified_sentinel
#check @FiniteOrdinaryEdgeChecks.rejected_conjunction_retains_allocation_and_emits_certified_sentinel
#print axioms FiniteOrdinaryEdgeChecks.accepted_conjunction_uses_actual_combined_and_zipped_requests
#check @FiniteOrdinaryEdgeChecks.accepted_conjunction_uses_actual_combined_and_zipped_requests
