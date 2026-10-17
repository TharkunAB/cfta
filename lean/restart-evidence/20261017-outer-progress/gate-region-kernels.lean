import MicroCFTA.SourceCurrentGatePlainRegion
import MicroCFTA.SourceEqualityAnnotationHeap

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000

namespace MicroCFTA.GatePlainRegionKernels
open InternedConstructorTemplates InternedNestedConstruction InternedProbeProvenance
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Plain" => fun guard => SourceMemoGate.plain guard = true

private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq)
    (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)

private def plainGuard : Guard := ⟨some [], .top⟩
private def constrainedGuard : Guard := ⟨some [[[0], [1]]], .top⟩
private def expression : Syntax Symbol Guard := .node [.mk ("roots", .top) plainGuard [
  .binder false (.node [.mk ("step", .top) plainGuard [.var 0]]),
  .binder false (.node [.mk ("pair", .top) constrainedGuard [.var 0, .var 0]])]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Value Symbol Guard := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def selected : Value Symbol Guard := ((children root)[0]?).getD .empty
private def other : Value Symbol Guard := ((children root)[1]?).getD .empty
private theorem built_done : built = .done root heap := by cbv
private theorem facts : InternedNestedFacts.Facts heap :=
  (InternedFreshOrdinaryFacts.closed_verified expression).facts
private theorem root_available : Available heap root :=
  (InternedFreshOrdinaryFacts.closed_verified expression).result root heap built_done
private theorem selected_available : Available heap selected :=
  root_available.children selected (by cbv; exact List.mem_cons_self)
private theorem other_available : Available heap other :=
  root_available.children other (by cbv; exact List.mem_cons_of_mem _ List.mem_cons_self)

/-- One actual heap has a gate-accepted region and a separate constrained recursive root. -/
theorem selected_region_without_global_plain :
    ∃ (program : Syntax Symbol Guard) (root selected other : Value Symbol Guard)
        (heap : State Symbol Guard),
      InternedFreshOrdinaryConstruction.build program [] empty = .done root heap ∧
      InternedNestedFacts.Facts heap ∧ Available heap selected ∧ Available heap other ∧
      SourceMemoGate.unconstrained selected = true ∧ SourceMemoGate.unconstrained other = false ∧
      SourceEqualityAnnotationLanguage.Annotated Plain selected ∧
      SourceEqualityPartialPlainRegion.Region selected ∧
      ¬ SourceEqualityAnnotationHeap.Heap Plain heap := by
  have accepted : SourceMemoGate.unconstrained selected = true := by cbv
  have refused : SourceMemoGate.unconstrained other = false := by cbv
  refine ⟨expression, root, selected, other, heap, built_done, facts, selected_available,
    other_available, accepted, refused,
    SourceCurrentGatePlainRegion.annotations heap selected facts.coherent selected_available accepted,
    SourceCurrentGatePlainRegion.region heap selected facts selected_available (by cbv) accepted, ?_⟩
  intro globallyPlain
  have annotated := SourceEqualityAnnotationHeap.available Plain heap globallyPlain facts.linked other other_available
  have impossible := SourceCurrentHereditaryUnconstrained.unconstrained other annotated
  rw [refused] at impossible
  cases impossible

end MicroCFTA.GatePlainRegionKernels

#check @MicroCFTA.GatePlainRegionKernels.selected_region_without_global_plain
#print axioms MicroCFTA.GatePlainRegionKernels.selected_region_without_global_plain
