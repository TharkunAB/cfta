import MicroCFTA.SourceCurrentAllocatedNativeAdmissionEdgeCertificates
import MicroCFTA.SourceCurrentAllocatedNativePairAdmission

open MicroCFTA Cache Language IntersectSchedule InternedConstructorTemplates
open InternedProbeProvenance InternedNestedProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView SourceCurrentAllocatedNativeAdmissionCache
open SourceCurrentAllocatedNativeAdmissionCode SourceCurrentAllocatedNativeAdmissionEdgeCertificates
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)

#print axioms children_certified
#print axioms sentinel_certified
#print axioms body_certified
#check @children_certified
#check @sentinel_certified
#check @body_certified

private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq) (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)

private def symbol : Symbol := ("a", .top)
private def actual := run (makeEdge symbol top []) empty
private def source : InternedConstructorTemplates.State Symbol Guard := actual.2
private def edge : EdgeValue Symbol Guard := actual.1
private theorem verified : InternedNestedFacts.Verified empty
    (InternedNestedConstruction.work (makeEdge symbol top []) empty) EdgeResident :=
  InternedNestedFacts.edge_verified symbol top [] empty InternedNestedFacts.empty_facts
    (by intro value member; cases member)
private theorem facts : InternedNestedFacts.Facts source := verified.facts
private theorem resident : EdgeResident source edge := verified.result _ _ rfl
private theorem edge_children : edge.children = [] := by cbv
private def machine : Machine Symbol Guard := ⟨source, Cache.emptyState⟩
private theorem valid : SourceRecursiveIntersectionKernel.Valid machine := ⟨facts, Cache.empty_valid⟩
private theorem emptySemantic : SourceEqualityRequiredSemanticCache.SemanticReady
    (InternedConstructorTemplates.empty : InternedConstructorTemplates.State Symbol Guard) :=
  SourceEqualityRequiredSemanticCache.constructed .empty .empty empty
    (by simp only [InternedFreshOrdinaryConstruction.build])
private theorem semantic : SourceEqualityRequiredSemanticCache.SemanticReady source :=
  SourceEqualityRequiredSemanticCache.edge symbol top [] empty emptySemantic (by intro value member; cases member)
private def holds (_ : Guard) (_ : Term Symbol) := true
private def roots : List (Value Symbol Guard) := [.empty]
private theorem originals : ∀ value ∈ roots, Original value := by
  intro value member
  have same := List.mem_singleton.mp member
  subst value
  exact .empty
private theorem available : Values source roots := by
  intro value member
  have same := List.mem_singleton.mp member
  subst value
  exact empty_available _
private theorem closed : ∀ value ∈ roots, value.free = [] := by
  intro value member
  have same := List.mem_singleton.mp member
  subst value
  rfl
private def inputs := SourceCurrentAllocatedNativeInputInventoryModels.finiteInput
  source facts holds roots originals available closed
private def request : EdgeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, edge, edge⟩
private theorem scope : EdgeScope source request := by
  refine ⟨resident, resident, ?_, ?_, ?_⟩
  · intro child member
    change child ∈ edge.children at member
    rw [edge_children] at member
    cases member
  · intro child member
    change child ∈ edge.children at member
    rw [edge_children] at member
    cases member
  · intro name member
    cases member
private theorem known : EdgeCovered inputs request := by
  refine ⟨⟨?_, ?_⟩, SourceCurrentAllocatedNativePairAdmission.empty_seen inputs⟩
  · intro child member
    change child ∈ edge.children at member
    rw [edge_children] at member
    cases member
  · intro child member
    change child ∈ edge.children at member
    rw [edge_children] at member
    cases member
private theorem ready : EdgeReady machine request := ⟨empty_domain _, resident, resident⟩
private noncomputable def before : SourceEqualityNativeDemand.State 8 :=
  ⟨initial 8 machine, SourceEqualityMkEdgeAllocation.emptyField SourceEqualityConstraintMemoAllocation.empty⟩
private noncomputable def observed := SourceEqualityNativeDemand.body request .pure before
private noncomputable def emitted : Code Symbol Guard (EdgeValue Symbol Guard) := match observed with
  | .yielded (.code code) _ => code
  | _ => .fail .exhausted
private noncomputable def after := observed.state
private theorem yielded : SourceEqualityNativeDemand.body request .pure before = .yielded (.code emitted) after := by cbv

example : edge.children = [] := edge_children
example : Certified source holds inputs (SourceEqualityNativeCheckedCode.sentinel edge) machine
    (fun final value => EdgeResident final.heap value) :=
  sentinel_certified source holds inputs edge machine valid
example (combined : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula) :
    Certified source holds inputs (SourceEqualityNativeCheckedCode.children request.domain request.left request.right combined)
      machine (fun final value => EdgeResident final.heap value) :=
  children_certified source facts holds inputs request scope known combined machine valid semantic ready
example : SourceEqualityNativeDemand.body request .pure before = .yielded (.code emitted) after := yielded
example : Certified source holds inputs emitted after.native.machine (fun final value => EdgeResident final.heap value) :=
  body_certified source facts holds inputs request scope known before after emitted valid semantic ready yielded
example : after.native = before.native := by
  simpa only [yielded, SourceEqualityNativeDemand.Outcome.state] using
    SourceEqualityNativeDemandOperations.body_native request .pure before

-- A literal unequal-arity observation emits a sentinel before field loads.
private def mismatched : EdgeRequest Symbol Guard :=
  ⟨request.domain, request.left, .mk request.right.entry [.empty]⟩
example : SourceEqualityNativeDemand.body mismatched .pure before = SourceEqualityNativeDemand.sentinel mismatched .pure before := by
  apply SourceEqualityNativeDemand.body_mismatch
  change edge.children.length ≠ 1
  rw [edge_children]
  decide
