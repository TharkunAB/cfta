import MicroCFTA.SourceCurrentConstrainedCapCheckedJointComputedQuery
import MicroCFTA.SourceCurrentConstrainedCapGuardExecution
import MicroCFTA.SourceCurrentHereditaryConstruction
import MicroCFTA.InternedValueMassConstructors
import MicroCFTA.SourceRecursiveIntersectionOriginalOutput
import MicroCFTA.SourceCurrentAllocatedNativeCompletedMemo
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

namespace MicroCFTA.GeneratedComputedKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand IntersectSchedule SourceRecursiveIntersectionInputView
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
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
private def before : Checked 26 := ⟨initial 26 machine, operations⟩
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

open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConstrainedCapKernelJoint (Context)
open SourceCurrentConstrainedCapCheckedJointClosed (Plain)
local notation "JointReceipt" => SourceCurrentConstrainedCapCheckedJointInventoryQuery.Receipt
local notation "Cap" => SourceCurrentConstrainedCap.Cap
private def sourceMass := InternedValueMassHeap.initialBound heap
private def amount := SourceCurrentAllocatedNativeComputedBudget.instructionBound heap.nodes.next heap.edges.next sourceMass
private def nodeControl : Control (Value Symbol Guard) := .code (requestNode request.domain left right)
private def inventory : Inventory := ⟨empty, InternedNestedFacts.empty_facts, [],
  (by intro value member; cases member), (by intro value member; cases member),
  (by intro value member; cases member)⟩

private theorem annotated_root : SourceEqualityAnnotationLanguage.Annotated Plain root := by
  have plainTop : Plain top := SourceCurrentUnconstrainedGuardClosure.top_plain
  have allowed : SourceEqualityAnnotationConstruction.Allowed Plain expression := by
    simp [expression, base, SourceEqualityAnnotationConstruction.Allowed,
      SourceEqualityAnnotationConstruction.EdgesAllowed, SourceEqualityAnnotationConstruction.ManyAllowed, plainTop]
  obtain ⟨value, state, done, _stored, annotated⟩ := SourceCurrentHereditaryConstruction.closed Plain expression allowed
  obtain ⟨sameValue, sameState⟩ := InternedNestedConstruction.Outcome.done.inj (constructed.symm.trans done)
  subst value
  subst state
  exact annotated

private theorem annotated_child (value : Value Symbol Guard) (member : value ∈ children root) :
    SourceEqualityAnnotationLanguage.Annotated Plain value := by
  have shape : ∃ entry rows depth free, root = .node entry rows depth free := ⟨_, _, _, _, by cbv⟩
  obtain ⟨entry, rows, depth, free, same⟩ := shape
  have annotated : SourceEqualityAnnotationLanguage.Annotated Plain (.node entry rows depth free) := by
    simpa only [same] using annotated_root
  cases annotated with
  | node _ _ _ _ _ known => exact known value (by simpa only [same, children] using member)

/-- A source built after an empty inventory constructs its own generated joint return with exact language and computed resources. -/
theorem constructed_generated_query
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    built = .done root heap ∧ inventory.source = empty ∧ inventory.roots = [] ∧ left ≠ right ∧
    ∃ (next : Inventory), ∃ fuel value after,
      next.source = heap ∧ next.roots = [left, right] ∧
      JointReceipt next 2 formulas solver fuel left right before value after ∧ At formulas solver next after ∧
      Cap Plain 2 value ∧
      (∀ ambient term, InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient value term ↔
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient left term ∧
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient right term) ∧
      fuel ≤ amount ∧ execute (amount + 1) nodeControl before = .done value after ∧
      InternedValueMassHeap.Stored (SourceCurrentAllocatedRecursiveMassTrace.massAfter amount sourceMass) after.native.machine.heap ∧
      InternedValueMass.value value ≤ SourceCurrentAllocatedRecursiveMassTrace.massAfter amount sourceMass ∧
      after.native.machine.heap.nodes.next ≤ heap.nodes.next + SourceCurrentAllocatedRecursiveMassTrace.credit amount sourceMass ∧
      after.native.machine.heap.edges.next ≤ heap.edges.next + SourceCurrentAllocatedRecursiveMassTrace.credit amount sourceMass ∧
      after.native.machine.domains.next ≤ before.native.machine.domains.next + amount := by
  have physical := InternedFreshOrdinaryFacts.closed_verified expression
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression root heap constructed
  have growth : Grows inventory.source heap := physical.growth
  have history : Extends inventory.source.nodes.issued heap.nodes.issued := physical.history
  have current : At formulas solver inventory before :=
    SourceCurrentAllocatedNativeInventoryState.initial inventory formulas solver 26 machine operations growth history
  have guards : SourceCurrentConstrainedCapGuardHeap.Heap Plain heap :=
    SourceCurrentConstrainedCapGuardExecution.closed_heap Plain expression
  have context : Context Plain inventory.source machine :=
    ⟨initial_good.native.machine, semantic.ready.semantic, guards, growth, history⟩
  have leftCap : Cap Plain 2 left := .plain 2 (annotated_child left (by cbv; exact .head _))
  have rightCap : Cap Plain 2 right := .plain 2 (annotated_child right (by cbv; exact .tail _ (.head _)))
  let next := SourceCurrentAllocatedNativeInventoryRebase.extend inventory heap initial_good.native.machine.1
    current.growth current.history left right originals.1 originals.2 (by cbv) (by cbv)
  obtain ⟨fuel, value, after, receipt, count, done, stored, mass, nodes, edges, domains⟩ :=
    SourceCurrentConstrainedCapCheckedJointComputedQuery.generated_complete 24 2 formulas solver inventory before
      initial_good current semantic context
      (SourceCurrentConstrainedCapCheckedJointCache.initial_stored Plain inventory.source 26 machine)
      (SourceCurrentConstrainedCapCheckedJointOrigins.initial_stored inventory.source 26 machine)
      (SourceCurrentAllocatedNativeScopeCache.initial_scoped 26 machine)
      (SourceRecursiveIntersectionNative.idle_initial machine) left right originals.1 originals.2 (by cbv) (by cbv)
      leftCap rightCap (InternedValueMassHeap.initial heap initial_good.native.machine.1) (by cbv) (by cbv) (by cbv)
  refine ⟨constructed, rfl, rfl, ?_, next, fuel, value, after, rfl, rfl,
    receipt, receipt.inventoryAt, receipt.cap, receipt.meaning, count, done, stored, mass, nodes, edges, domains⟩
  intro same
  have refs := congrArg Value.referenceOf same
  cbv at refs
  cases refs

end MicroCFTA.GeneratedComputedKernels

#print axioms MicroCFTA.GeneratedComputedKernels.constructed_generated_query
#check @MicroCFTA.GeneratedComputedKernels.constructed_generated_query
