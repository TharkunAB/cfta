import MicroCFTA.SourceEqualityNativeCheckedInstructionCredit
import MicroCFTA.SourceCurrentAllocatedNativePhysicalCompletion
import MicroCFTA.SourceCurrentAllocatedNativeFieldClosure
import MicroCFTA.SourceRecursiveIntersectionOriginalOutput
import MicroCFTA.InternedFreshOrdinaryClosedCompletion

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000

namespace MicroCFTA.CompileCostCheckedKernel
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open InternedNestedConstruction (Syntax)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq

private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq) (FormulaOrder.formula_eq first second)
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)

private def top : Guard := SourceEqualityConstraintConstructors.top
private def base : Syntax Symbol Guard := .node [.mk ("base", .top) top []]
private def expression : Syntax Symbol Guard := .node [.mk ("roots", .top) top [
  .node [.mk ("step", .top) top [base]],
  .node [.mk ("step", .top) top [base], .mk ("other", .top) top []]]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Value Symbol Guard := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def left : Value Symbol Guard := ((children root)[0]?).getD .empty
private def right : Value Symbol Guard := ((children root)[1]?).getD .empty
private def machine : Machine Symbol Guard := ⟨heap, Cache.emptyState⟩
private def operations := SourceEqualityMkEdgeAllocation.emptyField SourceEqualityConstraintMemoAllocation.empty
private def before : Checked 10 := ⟨initial 10 machine, operations⟩
private def request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩

private theorem constructed : built = .done root heap := by
  obtain ⟨value, state, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  simp only [built, root, heap, done, InternedNestedConstruction.Outcome.state]

private theorem initial_good : Good before := by
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression root heap constructed
  have guarded : SourceEqualityAnnotationHeap.Heap (fun guard : Guard => guard = top) heap := by
    have checked := SourceEqualityAnnotationConstruction.build (fun guard : Guard => guard = top) expression
      (by simp [expression, base, SourceEqualityAnnotationConstruction.Allowed,
        SourceEqualityAnnotationConstruction.EdgesAllowed, SourceEqualityAnnotationConstruction.ManyAllowed]) [] empty
      (SourceEqualityAnnotationHeap.empty_heap _)
    simpa only [built, heap] using checked
  have loaded := SourceCurrentConjunctionFieldAllocation.empty_field (Formula := FullSyntax.Formula) SourceEqualityConstraintMemoAllocation.empty
    SourceEqualityConstraintMemoAllocation.empty_valid
  refine ⟨SourceCurrentAllocatedNativePhysicalCache.initial_valid machine
    ⟨semantic.ready.semantic.1.normal.facts, Cache.empty_valid⟩, semantic.ready, loaded.1, ?_⟩
  intro key row found
  have same := guarded key row found
  rw [same]
  exact loaded.2.2

private theorem originals : Available heap left ∧ Available heap right := by
  have available := (InternedFreshOrdinaryFacts.closed_verified expression).result root heap constructed
  constructor
  · exact available.children left (by cbv; exact .head _)
  · exact available.children right (by cbv; exact .tail _ (.head _))

private theorem node_ready : NodeReady machine request := ⟨empty_domain machine, originals.1, originals.2⟩

private def row : EdgeValue Symbol Guard := match left with
  | .node _ (row :: _) _ _ => row
  | _ => (run (makeEdge ("unused", .top) top []) empty).1
private def edgeRequest : EdgeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, row, row⟩
private def startsNode : Code Symbol Guard (EdgeValue Symbol Guard) → Bool
  | .node .. => true
  | _ => false

/-- Actual loaded equality fields emit nonempty child code with credit from the independently derived original semantic rank. -/
theorem actual_checked_children :
    built = .done root heap ∧
    ∃ complete : IntersectSchedule.Completes (SourceRecursiveIntersectionInputView.view heap (fun _ _ => true))
        (SourceRecursiveIntersectionNative.edgeSemantic (fun _ _ => true) edgeRequest),
      ∃ code after,
        body edgeRequest .pure before = .yielded (.code code) after ∧
        startsNode code = true ∧ after.native = before.native ∧
        SourceRecursiveIntersectionInstructionCredit.At heap (fun _ _ => true)
          (SourceRecursiveIntersectionInstructionProfile.sourceBranching heap) code after.native.machine
          (1 + SourceRecursiveIntersectionInstructionProfile.sourceBranching heap *
            SourceRecursiveIntersectionInstructionProfile.budget
              (SourceRecursiveIntersectionInstructionProfile.sourceBranching heap)
              (IntersectSchedule.requiredFuel (SourceRecursiveIntersectionInputView.view heap (fun _ _ => true))
                (SourceRecursiveIntersectionNative.edgeSemantic (fun _ _ => true) edgeRequest) complete - 1))
          (fun final edge => EdgeResident final.heap edge) := by
  have facts := initial_good.native.machine.1
  have leftClosed : left.free = [] := by cbv
  have rightClosed : right.free = [] := by cbv
  have firstOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original left heap facts.coherent originals.1 leftClosed
  have secondOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original right heap facts.coherent originals.2 rightClosed
  have scope := SourceRecursiveIntersectionCode.initial_scope heap left right firstOriginal secondOriginal originals.1 originals.2
  have complete := SourceRecursiveIntersectionRequestProgress.initial_complete heap facts (fun _ _ => true)
    left right firstOriginal secondOriginal originals.1 originals.2 leftClosed rightClosed
  have bounded := SourceRecursiveIntersectionCode.compileNode_below heap facts (fun _ _ => true)
    request scope complete machine initial_good.native.machine node_ready (grows_refl _) (extends_refl _)
  change SourceRecursiveIntersectionCode.EdgeBelow heap (fun _ _ => true)
    (IntersectSchedule.requiredFuel (SourceRecursiveIntersectionInputView.view heap (fun _ _ => true))
      (SourceRecursiveIntersectionNative.nodeSemantic request) complete) edgeRequest ∧ _ at bounded
  obtain ⟨edgeScope, edgeComplete, _smaller⟩ := bounded.1
  have resident : EdgeReady machine edgeRequest := by
    exact ⟨empty_domain _, edgeScope.leftResident, edgeScope.rightResident⟩
  obtain ⟨code, operations, yielded, _valid, _growth, _fields, _codeFields⟩ :=
    SourceCurrentAllocatedNativeFieldClosure.body_complete edgeRequest .pure before initial_good.operations
      initial_good.fields resident (fun _ => trivial)
  let after : Checked 10 := {before with operations := operations}
  have checked := SourceEqualityNativeCheckedInstructionCredit.body_at heap facts (fun _ _ => true)
    edgeRequest edgeScope edgeComplete before after code initial_good.native.machine resident yielded
  have selected : (match body edgeRequest .pure before with
    | .yielded (.code code) _ => startsNode code
    | _ => false) = true := by
    set_option cbv.maxSteps 200000000 in cbv
  have starts : startsNode code = true := by simpa only [yielded] using selected
  exact ⟨constructed, edgeComplete, code, after, yielded, starts, checked⟩

end MicroCFTA.CompileCostCheckedKernel

namespace MicroCFTA.CompileCostSourceKernel
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView SourceRecursiveIntersectionNative IntersectSchedule
open SourceRecursiveIntersectionInstructionProfile (budget sourceBranching)
open InternedNestedConstruction (Syntax Outcome)

private def fixture : Syntax Nat Bool :=
  .node [.mk 99 true [
    .binder false (.node [.mk 0 true [.var 0]]),
    .union [.binder false .empty, .node [.mk 1 false []]],
    .node [.mk 2 true []], .node [.mk 2 false []]]]
private def kind : Value Nat Bool → Nat
  | .empty => 0
  | .reference _ => 1
  | .node _ _ _ _ => 2
  | .union _ _ _ _ => 3
  | .mu _ _ _ _ => 4

/-- Original mixed source construction derives complete compiler credit for every ordered root-child request. -/
theorem mixed_source_dispatch :
    ∃ root heap,
      InternedFreshOrdinaryConstruction.build fixture [] empty = .done root heap ∧
      ((children root).map kind) = [4, 3, 2, 2] ∧
      ∀ left ∈ children root, ∀ right ∈ children root,
        ∃ complete : Completes (view heap (fun _ _ => true))
          (nodeSemantic ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩),
        SourceRecursiveIntersectionInstructionCredit.At heap (fun _ _ => true) (sourceBranching heap)
          (SourceRecursiveIntersectionCode.compileNode ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩)
          ⟨heap, Cache.emptyState⟩
          (2 + sourceBranching heap * budget (sourceBranching heap)
            (requiredFuel (view heap (fun _ _ => true))
              (nodeSemantic ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩) complete - 1))
          (fun after value => Available after.heap value) := by
  obtain ⟨root, heap, built⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete fixture
  have verified := InternedFreshOrdinaryFacts.closed_verified fixture
  have facts : Facts heap := by simpa only [built, InternedNestedConstruction.Outcome.state] using verified.facts
  have available := verified.result root heap built
  have sourceKinds : (match InternedFreshOrdinaryConstruction.build fixture [] empty with
    | .done value _ => decide ((children value).map kind = [4, 3, 2, 2])
    | _ => false) = true := by cbv
  have sourceClosed : (match InternedFreshOrdinaryConstruction.build fixture [] empty with
    | .done value _ => decide ((children value).map Value.free = [[], [], [], []])
    | _ => false) = true := by cbv
  have kinds : (children root).map kind = [4, 3, 2, 2] := by simpa only [built, decide_eq_true_eq] using sourceKinds
  have closed : (children root).map Value.free = List.replicate 4 [] := by
    change (children root).map Value.free = [[], [], [], []]
    simpa only [built, decide_eq_true_eq] using sourceClosed
  have allClosed : ∀ value ∈ children root, value.free = [] := by
    intro value member
    have inside : value.free ∈ (children root).map Value.free := List.mem_map.mpr ⟨value, member, rfl⟩
    rw [closed] at inside
    exact List.eq_of_mem_replicate inside
  refine ⟨root, heap, built, kinds, ?_⟩
  intro left leftMember right rightMember
  have leftAvailable := available.children left leftMember
  have rightAvailable := available.children right rightMember
  have leftOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original left heap facts.coherent leftAvailable (allClosed left leftMember)
  have rightOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original right heap facts.coherent rightAvailable (allClosed right rightMember)
  have scope := initial_scope heap left right leftOriginal rightOriginal leftAvailable rightAvailable
  have complete := SourceRecursiveIntersectionRequestProgress.initial_complete heap facts (fun _ _ => true)
    left right leftOriginal rightOriginal leftAvailable rightAvailable (allClosed left leftMember) (allClosed right rightMember)
  exact ⟨complete, SourceRecursiveIntersectionCompileInstructionCredit.compileNode heap facts (fun _ _ => true) _ scope complete
    ⟨heap, Cache.emptyState⟩ ⟨facts, Cache.empty_valid⟩ ⟨empty_domain _, leftAvailable, rightAvailable⟩
    (grows_refl _) (extends_refl _)⟩

end MicroCFTA.CompileCostSourceKernel

#print axioms MicroCFTA.CompileCostCheckedKernel.actual_checked_children
#check @MicroCFTA.CompileCostCheckedKernel.actual_checked_children
#print axioms MicroCFTA.CompileCostSourceKernel.mixed_source_dispatch
#check @MicroCFTA.CompileCostSourceKernel.mixed_source_dispatch
