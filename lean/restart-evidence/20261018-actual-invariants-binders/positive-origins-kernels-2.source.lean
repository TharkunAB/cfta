import MicroCFTA.SourceCurrentPositiveClassOrigins
import MicroCFTA.SourceCurrentOuterParentHeightGrowth
set_option linter.all true
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 30000000

namespace MicroCFTA.PositiveClassOriginKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Syntax)
open SourceCurrentAllocatedPartialState
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Ops" => SourceEqualityConstraintMemoAllocation.State
local notation "prefix" => SourceCurrentAllocatedInheritedPrefix.run

private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq)
    (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)

private theorem array_small (classes : EqualityNormalize.Constraints) :
    SourceCompactGuards.arrayNormalize classes = SourceEqualityNormalizationReceipt.observed 16 classes :=
  SourceEqualityNormalizationReceipt.observed_eq 16 classes
attribute [local cbv_eval] array_small

private def plain : Guard := ⟨some [], .top⟩
private def selected : Guard :=
  ⟨some [],.and [.same [0,0] [0,1],.and [.top,.same [0,1] [0,2]]]⟩
private def raw : EqualityNormalize.Constraints := [[[0,0],[0,1]],[[0,1],[0,2]]]
private theorem extracted : SourceCompactGuards.positive selected.guard = some raw := by cbv
private theorem normalized : SourceCompactGuards.sourceEqualities selected =
    some [[[0,0],[0,1],[0,2]]] := by cbv

private def leaf : Syntax Symbol Guard := .node [.mk ("leaf",.top) plain []]
private def finite : Syntax Symbol Guard := .node [.mk ("pair",.top) plain [leaf,leaf,leaf]]
private def recursive : Syntax Symbol Guard :=
  .binder false (.node [.mk ("leaf",.top) plain [], .mk ("pair",.top) plain [.var 0,.var 0]])
private def expression : Syntax Symbol Guard := .node [.mk ("root",.top) selected [finite,recursive]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def original : Value Symbol Guard := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def values := children original
private def ownAllocation := SourceEqualityConstraintAllocation.construct selected.equalities Cache.emptyState
private def own : EqValue := match ownAllocation.1 with | .ok value => value | _ => .contradiction
private def emptyAllocation := SourceEqualityConstraintAllocation.construct plain.equalities ownAllocation.2
private def top : EqValue := match emptyAllocation.1 with | .ok value => value | _ => .contradiction
private def before := SourceCurrentAllocatedPartialInitialization.caller 8 emptyAllocation.2 heap
private def rootRequest : NodeRequest := ⟨top,original⟩
private def running := (beginNode rootRequest before).2.2
private noncomputable def combined := match (prefix selected top running.checked.operations).1 with
  | .ok (some value) => value | _ => .contradiction
private noncomputable def child := SourceEqualityConstraintMemoAllocation.descend combined 0
  (prefix selected top running.checked.operations).2

private theorem cached : SourceEqualityGuardReadback.Cached selected.equalities :=
  SourceEqualityGuardReadback.empty_cached

private theorem history : SourceEqualityOriginalAllocationHistory.History Cache.emptyState
    emptyAllocation.2 [selected,plain] := by
  have first : SourceEqualityOriginalAllocationHistory.History Cache.emptyState ownAllocation.2 [selected] := by
    simpa only [List.nil_append] using SourceEqualityOriginalAllocationHistory.History.construct
      (.start Cache.emptyState) cached (show ownAllocation = (.ok own,ownAllocation.2) by cbv)
  exact SourceEqualityOriginalAllocationHistory.History.construct first SourceEqualityGuardReadback.empty_cached
    (show emptyAllocation = (.ok top,emptyAllocation.2) by cbv)

private theorem built_done : built = .done original heap := by cbv

private theorem covered : ∀ guard ∈ SourceEqualityConstraintOrigins.guards expression, guard ∈ [selected,plain] := by
  intro guard member
  simp only [expression,finite,leaf,recursive,SourceEqualityConstraintOrigins.guards,
    SourceEqualityConstraintOrigins.edgeGuards,SourceEqualityConstraintOrigins.childGuards,
    List.mem_cons,List.mem_append,List.not_mem_nil,or_false,or_assoc,false_or] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- A source-built selected class allocates an actual child key distinct from its active Top root. -/
private theorem checked_initial_dispatch (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    SourceCurrentConjunctionClassScan.Ready before.checked ∧
    Available heap original ∧
    SourceCurrentAllocatedGateWorker.primary 16 values [[0,0],[0,1]] before.checked = .done false before.checked ∧
    beginNode rootRequest before = (0,.evaluate rootRequest,running) ∧
    running.nodeResults.cells 0 = some ⟨rootRequest,.evaluating⟩ ∧
    (prefix selected top running.checked.operations).1 = .ok (some combined) ∧
    child.1.payload ≠ some [] ∧
    (NodeRequest.mk child.1 ((values[0]?).getD .empty)).key ≠ rootRequest.key := by
  have initial := SourceCurrentAllocatedPartialInitialization.constructed 8 history Cache.empty_valid
    expression covered original heap built_done formulas solver
  obtain ⟨identity, emptyIsTop, topReady, available, _, _⟩ := initial.2
  have sameTop : top = .live identity [] := by
    have literal : top = SourceCurrentAllocatedPartialInitialization.emptyValue emptyAllocation.2 := by cbv
    exact literal.trans emptyIsTop
  have initialTop : SourceEqualityConstraintAllocation.Ready running.checked.operations.constraints top := by
    rw [sameTop]
    exact topReady
  have field : SourceCurrentConjunctionEquality.FieldAvailable running.checked.operations selected := by
    have load := SourceEqualityConstraintFieldLookup.load_of_construct selected cached Cache.emptyState Cache.empty_valid
      own ownAllocation.2 (show ownAllocation = (.ok own,ownAllocation.2) by cbv)
    have next := history.verified Cache.empty_valid
    have growth := (SourceCurrentAllocatedPartialInitialization.operations_correct emptyAllocation.2 next.1).2.1
    have ownField : SourceCurrentConjunctionEquality.FieldAvailable
        (SourceEqualityConstraintMemoAllocation.initial ownAllocation.2) selected := ⟨cached,_,load.1⟩
    obtain ⟨emptyValue,cache,done,_,_,steps,_,_⟩ := SourceEqualityConstraintAllocation.construct_complete
      plain.equalities SourceEqualityGuardReadback.empty_cached ownAllocation.2 load.2.2.2.2
    have sameCache : cache = emptyAllocation.2 := congrArg Prod.snd done.symm
    have firstGrowth : SourceEqualityConstraintMemoAllocation.Grows
        (SourceEqualityConstraintMemoAllocation.initial ownAllocation.2)
        (SourceEqualityConstraintMemoAllocation.initial emptyAllocation.2) :=
      ⟨sameCache ▸ steps,
        Cache.extends_refl _,Cache.extends_refl _⟩
    exact (ownField.grows firstGrowth).grows growth
  obtain ⟨output,actual,valid,ready,growth,childValid,childReady,childGrowth,nonempty⟩ :=
    SourceCurrentPositiveClassOrigins.field_split selected top running.checked.operations
      initial.1.ready.good.operations initialTop field raw extracted [[0,0],[0,1]]
      (by simp [raw]) 0 [0] [1] (by simp) (by simp) (by decide)
  have exactCombined : output = combined := by
    unfold combined
    rw [actual]
  subst output
  have childNonempty : child.1.payload ≠ some [] := nonempty
  have distinct := SourceCurrentInheritedOwnerProgress.node_key_ne_top running.checked.operations child.2
    childValid (SourceCurrentConjunctionEquality.grows_trans growth childGrowth) child.1 childReady
    childNonempty identity topReady ((values[0]?).getD .empty) original
  refine ⟨initial.1.ready,available,?_,?_,?_,actual,childNonempty,?_⟩
  · cbv
  · cbv
  · cbv
  · simpa only [rootRequest,sameTop] using distinct

/-- A source-built empty stored field derives its nonempty child only from nested positive guards. -/
private theorem checked_positive_split (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    selected.equalities = some [] ∧
    SourceCompactGuards.positive selected.guard = some raw ∧
    SourceCompactGuards.sourceEqualities selected = some [[[0,0],[0,1],[0,2]]] ∧
    SourceCurrentConjunctionClassScan.Ready before.checked ∧
    Available heap original ∧
    SourceCurrentAllocatedGateWorker.primary 16 values [[0,0],[0,1]] before.checked = .done false before.checked ∧
    beginNode rootRequest before = (0,.evaluate rootRequest,running) ∧
    running.nodeResults.cells 0 = some ⟨rootRequest,.evaluating⟩ ∧
    (prefix selected top running.checked.operations).1 = .ok (some combined) ∧
    child.1.payload ≠ some [] ∧
    (NodeRequest.mk child.1 ((values[0]?).getD .empty)).key ≠ rootRequest.key :=
  ⟨rfl,extracted,normalized,checked_initial_dispatch formulas solver⟩

/-- The exact checked source-built positive guard example. -/
theorem initial_positive_split (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    selected.equalities = some [] ∧
    SourceCompactGuards.positive selected.guard = some raw ∧
    SourceCompactGuards.sourceEqualities selected = some [[[0,0],[0,1],[0,2]]] ∧
    SourceCurrentConjunctionClassScan.Ready before.checked ∧
    Available heap original ∧
    SourceCurrentAllocatedGateWorker.primary 16 values [[0,0],[0,1]] before.checked = .done false before.checked ∧
    beginNode rootRequest before = (0,.evaluate rootRequest,running) ∧
    running.nodeResults.cells 0 = some ⟨rootRequest,.evaluating⟩ ∧
    (prefix selected top running.checked.operations).1 = .ok (some combined) ∧
    child.1.payload ≠ some [] ∧
    (NodeRequest.mk child.1 ((values[0]?).getD .empty)).key ≠ rootRequest.key :=
  checked_positive_split formulas solver

end MicroCFTA.PositiveClassOriginKernels
