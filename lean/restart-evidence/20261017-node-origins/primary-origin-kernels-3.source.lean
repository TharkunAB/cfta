import MicroCFTA.SourceCurrentRequiredPrimaryOrigins
import MicroCFTA.SourceEqualityNormalizationReceipt

set_option linter.all true
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.RequiredPrimaryOriginKernels
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Syntax)
open InternedNestedProvenance (Values)
open SourceEqualityNeeded SourceEqualityRequiredGraph SourceEqualityRequiredSemanticCache
open SourceCurrentRequiredRowOrigins
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => State Symbol Guard
local notation "Plain" => fun guard : Guard => SourceMemoGate.plain guard = true
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source

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
private def own : Guard := ⟨some [[[0],[1]]], .top⟩
private def leaf : Syntax Symbol Guard := .node [.mk ("leaf", .top) plain []]
private def finite : Syntax Symbol Guard := .node [.mk ("pair", .top) own [leaf,leaf]]
private def recursive : Syntax Symbol Guard :=
  .binder false (.node [.mk ("leaf", .top) plain [], .mk ("pair", .top) plain [.var 0,.var 0]])
private def expression : Syntax Symbol Guard := .node [.mk ("roots", .top) plain [finite,recursive]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def original : Value Symbol Guard := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def b := ((children original)[0]?).getD (Value.empty : Value Symbol Guard)
private def tau := ((children original)[1]?).getD (Value.empty : Value Symbol Guard)
private def values : List (Value Symbol Guard) := [b,tau,.reference .depth]
private def paths : EqualityNormalize.Class := [[0,0],[0,1],[1,0]]
private def neededB : Needed := .node [(0,.node []),(1,.node [])]
private def neededTau : Needed := .node [(0,.node [])]
private def entries : List (Int × Needed) := [(0,neededB),(1,neededTau)]
private def row : EdgeValue Symbol Guard :=
  ((nodeEdges b)[0]?).getD (run (makeEdge ("pair",.top) own []) heap).1

private theorem built_done : built = .done original heap := by cbv
private theorem semantic : SemanticReady heap :=
  SourceEqualityRequiredSemanticCache.constructed expression original heap built_done
private theorem available_original : Available heap original :=
  (InternedFreshOrdinaryFacts.closed_verified expression).result original heap built_done
private theorem available_b : Available heap b :=
  available_original.children b (by cbv; exact List.mem_cons_self)
private theorem available_tau : Available heap tau :=
  available_original.children tau (by cbv; exact List.mem_cons_of_mem _ List.mem_cons_self)
private theorem available_values : Values heap values := by
  intro value member
  rcases List.mem_cons.mp member with rfl | member
  · exact available_b
  rcases List.mem_cons.mp member with rfl | member
  · exact available_tau
  · have same := List.mem_singleton.mp member
    subst value
    exact InternedNestedProvenance.depth_available heap
private theorem gate : EndpointStatefulGateTrace.ClassTrace source reaches values paths heap false heap := by
  have first : EndpointStatefulGateTrace.PathTrace source reaches values [0,0] heap false heap := by
    refine .child (.present (value := b) rfl ?_)
    exact .finite (by cbv)
  have second : EndpointStatefulGateTrace.PathTrace source reaches values [0,1] heap false heap := by
    refine .child (.present (value := b) rfl ?_)
    exact .finite (by cbv)
  have third : EndpointStatefulGateTrace.PathTrace source reaches values [1,0] heap false heap := by
    refine .child (.present (value := tau) rfl ?_)
    exact .closed (by cbv) (by cbv)
  exact .next first (.next second (.next third .nil))
private theorem costs : InternedFreshOrdinaryCostHeap.Heap heap := by
  simpa only [heap,built] using InternedFreshOrdinaryCosts.closed_heap expression
private theorem normal : SourceCurrentRequiredUnionNormal.UnionNormal heap := SourceCurrentRequiredUnionNormal.source expression
private theorem guards : SourceCurrentConstrainedCapGuardHeap.Heap Plain heap := by
  simpa only [heap,built] using
    SourceCurrentConstrainedCapGuardExecution.closed_heap Plain expression
private theorem compiled : build (paths.map (List.map Int.ofNat)) = .node entries := by cbv
private theorem b_fixed : RequireNode neededB b heap b heap := by
  apply (SourceEqualityRequiredExecution.node_execution_iff neededB b heap b heap).mpr
  exact ⟨4,0,by cbv⟩

private theorem decisions (first second : DecidableEq (EdgeKey Symbol Guard)) : first = second := by
  funext left right
  exact Subsingleton.elim _ _

/-- Initial false primary paths construct recursive exposure, retain B's positive row, and leave an open sibling untouched. -/
theorem selected_finite_and_recursive :
    ∃ (program : Syntax Symbol Guard) (initialValue finiteValue recursiveValue : Value Symbol Guard)
      (initial final : Heap) (recursiveResult : Value Symbol Guard) (positiveRow : EdgeValue Symbol Guard),
      InternedFreshOrdinaryConstruction.build program [] empty = .done initialValue initial ∧
      EndpointStatefulGateTrace.ClassTrace source reaches
        [finiteValue,recursiveValue,.reference .depth] [[0,0],[0,1],[1,0]] initial false initial ∧
      SourceEqualityRequiredWorkerComplete.StableRun
        (fun fuel reader => SourceEqualityRequiredExecution.requireAll fuel reader [[0,0],[0,1],[1,0]]
          [finiteValue,recursiveValue,.reference .depth] initial)
        [finiteValue,recursiveResult,.reference .depth] final ∧
      All₂ Origin [finiteValue,recursiveValue,.reference .depth]
        [finiteValue,recursiveResult,.reference .depth] ∧
      (∃ exposed middle, SourceEqualityRequiredHead.Head recursiveValue initial exposed middle) ∧
      RowAt finiteValue [] 0 positiveRow ∧
      SourceEqualityPhysicalPayload.own positiveRow.entry.key.constraint ≠ .ok (some []) ∧
      ∃ sourcePath sourceIndex sourceRow, RowAt finiteValue sourcePath sourceIndex sourceRow ∧
        SourceCurrentRequiredGuardOrigins.RowOrigin sourceRow positiveRow := by
  have producer := @SourceCurrentRequiredPrimaryOrigins.complete
  rw [decisions SourceCurrentRequiredPrimaryOrigins.instDecidableEqEdgeKeyLabelFormulaConstraint inferInstance] at producer
  obtain ⟨results,after,_kept,_semantic,_available,stable,origins,_language⟩ :=
    producer gate semantic costs available_values
      heap semantic normal costs guards available_values (grows_refl heap)
  obtain ⟨result,final,tauGraph,_keeps,_resident,_closed,_tauStable⟩ :=
    SourceEqualityRequiredExecution.complete neededTau tau heap semantic.ready available_tau (by cbv)
  have actual : RequireChildren entries 0 values heap [b,result,.reference .depth] final :=
    .selected 0 rfl b_fixed (.selected 1 rfl tauGraph (.unselected 2 rfl .nil))
  have chosen : SourceEqualityRequiredWorkerComplete.StableRun
      (fun fuel reader => SourceEqualityRequiredExecution.requireAll fuel reader
        (paths.map (List.map Int.ofNat)) values heap) [b,result,.reference .depth] final := by
    simpa only [SourceEqualityRequiredExecution.requireAll,compiled] using
      SourceEqualityRequiredWorkerComplete.children_stable actual
  obtain ⟨same,sameState⟩ := SourceEqualityRequiredExecution.stable_unique stable chosen
  subst results after
  have first : Origin b b := by cases origins with | cons first rest => exact first
  have occurrence : RowAt b [] 0 row := .root (by cbv)
  have positive : SourceEqualityPhysicalPayload.own row.entry.key.constraint ≠ .ok (some []) := by
    intro impossible
    have different : SourceEqualityPhysicalPayload.own row.entry.key.constraint = .ok (some [[[0],[1]]]) := by cbv
    rw [different] at impossible
    cases impossible
  have head : ∃ exposed middle, SourceEqualityRequiredHead.Head tau heap exposed middle := by
    cases tauGraph with
    | recursive _ _ head _ => exact ⟨_,_,head⟩
  refine ⟨expression,original,b,tau,heap,final,result,row,built_done,gate,stable,origins,head,occurrence,positive,?_⟩
  exact first.physical_positive occurrence positive

/-- The constructed endpoint leaves an unrelated open reference and productive Mu unchanged for every empty-requirement fuel. -/
theorem constructed_empty_open :
    ∃ (program : Syntax Symbol Guard) (value recursiveValue : Value Symbol Guard) (initial : Heap),
      InternedFreshOrdinaryConstruction.build program [] empty = .done value initial ∧
      recursiveValue.free = [] ∧ 0 < recursiveValue.depth ∧
      All₂ Origin [.reference .depth,recursiveValue] [.reference .depth,recursiveValue] ∧
      ∀ fuel reader, SourceEqualityRequiredExecution.requireAll fuel reader []
        [.reference .depth,recursiveValue] initial = .done [.reference .depth,recursiveValue] initial := by
  have producer := SourceCurrentRequiredPrimaryOrigins.constructed expression
  rw [decisions SourceCurrentRequiredPrimaryOrigins.instDecidableEqEdgeKeyLabelFormulaConstraint inferInstance] at producer
  obtain ⟨value,state,builtSource,complete⟩ := producer
  obtain ⟨same,sameState⟩ := InternedNestedConstruction.Outcome.done.inj (builtSource.symm.trans built_done)
  subst value state
  have available : Values heap [.reference .depth,tau] := by
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact InternedNestedProvenance.depth_available heap
    · have same := List.mem_singleton.mp member
      subst value
      exact available_tau
  obtain ⟨results,after,stable,origins,_language⟩ := complete [.reference .depth,tau] available [] .nil
  have identity : SourceEqualityRequiredWorkerComplete.StableRun
      (fun fuel reader => SourceEqualityRequiredExecution.requireAll fuel reader [] [.reference .depth,tau] heap)
      [.reference .depth,tau] heap :=
    ⟨0,0,fun fuel reader _ _ => SourceEqualityRequiredExecution.requireAll_identity fuel reader _ _⟩
  obtain ⟨same,sameState⟩ := SourceEqualityRequiredExecution.stable_unique stable identity
  subst results after
  refine ⟨expression,original,tau,heap,built_done,?_,?_,origins,?_⟩
  · cbv
  · cbv
  · intro fuel reader
    exact SourceEqualityRequiredExecution.requireAll_identity fuel reader _ _

end MicroCFTA.RequiredPrimaryOriginKernels

#check @MicroCFTA.RequiredPrimaryOriginKernels.selected_finite_and_recursive
#print axioms MicroCFTA.RequiredPrimaryOriginKernels.selected_finite_and_recursive
#check @MicroCFTA.RequiredPrimaryOriginKernels.constructed_empty_open
#print axioms MicroCFTA.RequiredPrimaryOriginKernels.constructed_empty_open
