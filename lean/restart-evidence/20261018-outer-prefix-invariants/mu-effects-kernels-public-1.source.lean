import MicroCFTA.SourceCurrentMuReconstructionEffects
import MicroCFTA.SourceCurrentConjunctionClassHistoryEntry

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
set_option cbv.maxSteps 1000000

namespace MicroCFTA.MuEffectsKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax)
open SourceCurrentAllocatedPartialState
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq) (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)
private noncomputable instance : DecidableEq (Value Symbol Guard) := by classical exact inferInstance
private def annotation : Guard := SourceEqualityConstraintConstructors.top
private def expression (used : Bool) : Syntax Symbol Guard :=
  .binder false (.node (if used then [
    .mk ("leaf",.top) annotation [],
    .mk ("pair",.top) annotation [.var 0,
      .binder false (.node [.mk ("nested",.top) annotation [.var 0,.var 1]])]]
    else [.mk ("leaf",.top) annotation []]))
private def built (used : Bool) := InternedFreshOrdinaryConstruction.build (expression used) [] empty
private def value (used : Bool) : Value Symbol Guard := match built used with | .done result _ => result | .pending .. => .empty
private def heap (used : Bool) := (built used).state
private def allocated := SourceEqualityConstraintAllocation.construct annotation.equalities Cache.emptyState
private def field : SourceEqualityConstraintAllocation.Value := match allocated.1 with | .ok own => own | .error _ => .contradiction
private def before (width : Nat) (used : Bool) : SourceEqualityNativeDemand.State width :=
  ⟨SourceRecursiveIntersectionThunks.initial width ⟨heap used,Cache.emptyState⟩,
    SourceEqualityConstraintMemoAllocation.initial allocated.2⟩
private def caller (width : Nat) (used : Bool) : SourceCurrentAllocatedPartialState.State width :=
  SourceCurrentAllocatedPartialState.initial (before width used) SourceCurrentMemoMergeGraph.empty SourceCurrentEmptinessMemo.empty
private def request (used : Bool) : NodeRequest := ⟨.contradiction,value used⟩
private def running (width : Nat) (used : Bool) := (beginNode (request used) (caller width used)).2.2
private theorem constructed (used : Bool) : built used = .done (value used) (heap used) := by
  obtain ⟨result,after,done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete (expression used)
  simp only [built,value,heap,done,InternedNestedConstruction.Outcome.state]
private theorem history : SourceEqualityOriginalAllocationHistory.History Cache.emptyState allocated.2 [annotation] := by
  have allocation : allocated = (.ok field,allocated.2) := by cbv
  simpa only [List.nil_append] using SourceEqualityOriginalAllocationHistory.History.construct
    (.start Cache.emptyState) SourceEqualityGuardReadback.empty_cached allocation
private theorem ready (width : Nat) (used : Bool) : SourceCurrentNativeOperationHeap.Good (before width used) ∧
    Available (heap used) (value used) := by
  have covered : ∀ original ∈ SourceEqualityConstraintOrigins.guards (expression used), original ∈ [annotation] := by
    cases used <;> simp [expression,SourceEqualityConstraintOrigins.guards,
      SourceEqualityConstraintOrigins.edgeGuards,SourceEqualityConstraintOrigins.childGuards]
  obtain ⟨initial,available,_⟩ := SourceCurrentConjunctionClassHistoryEntry.constructed width history Cache.empty_valid
    (expression used) covered (value used) (heap used) (constructed used)
  exact ⟨SourceCurrentNativeOperationHeap.Good.of_native
    (SourceCurrentNativeOperationInvariants.Good.of_checked initial.good) initial.semantic initial.costs,available⟩
private theorem mu_shape (used : Bool) : ∃ entry body depth ordinary, value used = .mu entry body depth ordinary := by
  have tag : (match value used with | .mu .. => True | _ => False) := by
    cases used <;> cbv
  cases shape : value used with
  | mu entry body depth ordinary => exact ⟨entry,body,depth,ordinary,rfl⟩
  | empty | node | union | reference => simp only [shape] at tag
private theorem zeroProof (width : Nat) (used : Bool) :
    beginNode (request used) (caller width used) = (0,.evaluate (request used),running width used) ∧
    SourceCurrentAllocatedPartialWorker.nodeBody 0 0 0 0 0 0 0 0 0 0 0
      (request used) (running width used) = .done (cleanup (value used)) (running width used) := by
  refine ⟨rfl,?_⟩
  obtain ⟨entry,body,depth,ordinary,shape⟩ := mu_shape used
  have probes := SourceCurrentMuReconstructionEffects.constructed (expression used) (value used) (heap used) (constructed used)
  have called := SourceCurrentMuReconstructionEffects.node_body 0 0 0 0 0 0 0 0 0 0 0 entry body depth ordinary
    .contradiction (running width used) (ready width used).1 probes (shape ▸ (ready width used).2)
  simpa only [request,← shape] using called

/-- A source-built used binder with a nested used binder completes with an active caller at zero fuel. -/
theorem used_zero (width : Nat) :
    beginNode (request true) (caller width true) = (0,.evaluate (request true),running width true) ∧
    SourceCurrentAllocatedPartialWorker.nodeBody 0 0 0 0 0 0 0 0 0 0 0
      (request true) (running width true) = .done (cleanup (value true)) (running width true) := zeroProof width true

/-- A source-built unused binder returns its smart cleanup at zero fuel and retains the active caller. -/
theorem unused_zero (width : Nat) :
    beginNode (request false) (caller width false) = (0,.evaluate (request false),running width false) ∧
    SourceCurrentAllocatedPartialWorker.nodeBody 0 0 0 0 0 0 0 0 0 0 0
      (request false) (running width false) = .done (cleanup (value false)) (running width false) := zeroProof width false
end MicroCFTA.MuEffectsKernels

#check @MicroCFTA.MuEffectsKernels.used_zero
#print MicroCFTA.MuEffectsKernels.used_zero
#print axioms MicroCFTA.MuEffectsKernels.used_zero
#check @MicroCFTA.MuEffectsKernels.unused_zero
#print MicroCFTA.MuEffectsKernels.unused_zero
#print axioms MicroCFTA.MuEffectsKernels.unused_zero
