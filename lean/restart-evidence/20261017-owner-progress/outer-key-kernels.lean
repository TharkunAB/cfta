import MicroCFTA.SourceCurrentOuterKeyIdentity
import MicroCFTA.SourceCurrentAllocatedPartialInitialization
import MicroCFTA.SourceCurrentAllocatedPartialWorker

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

namespace MicroCFTA.OuterKeyIdentityKernels
open InternedConstructorTemplates InternedNestedConstruction InternedProbeProvenance InternedEdgeResidency
open SourceCurrentAllocatedPartialState
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Eq" => SourceEqualityConstraintAllocation.Value
local notation "EqCache" => Cache.State SourceEqualityPartialConstraintKey.Key
local notation "Caller" => SourceCurrentAllocatedPartialState.State

private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq)
    (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)
private noncomputable instance : DecidableEq (Value Symbol Guard) := by classical exact inferInstance

private def plain : Guard := ⟨some [], .top⟩
private def expression : Syntax Symbol Guard := .node [.mk ("leaf", .top) plain []]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Value Symbol Guard := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def row : EdgeValue Symbol Guard :=
  ((nodeEdges root)[0]?).getD (run (makeEdge ("leaf", .top) plain []) heap).1
private def inherited := SourceCurrentAllocatedPartialInitialization.emptyValue Cache.emptyState
private def before := SourceCurrentAllocatedPartialInitialization.caller 8 Cache.emptyState heap
private def nodeRequest : NodeRequest := ⟨inherited, root⟩
private def edgeRequest : EdgeRequest := ⟨inherited, row⟩
private noncomputable def nodeRun := SourceCurrentAllocatedPartialWorker.nodeCall
  4 4 4 4 4 4 4 4 4 32 0 nodeRequest before
private noncomputable def middle := nodeRun.state
private noncomputable def edgeRun := SourceCurrentAllocatedPartialWorker.edgeCall
  4 4 4 4 4 4 4 4 4 32 0 edgeRequest middle
private noncomputable def after := edgeRun.state

private theorem built_done : built = .done root heap := by cbv
private theorem facts : InternedNestedFacts.Facts heap :=
  (InternedFreshOrdinaryFacts.closed_verified expression).facts
private theorem available : Available heap root :=
  (InternedFreshOrdinaryFacts.closed_verified expression).result root heap built_done
private theorem resident : EdgeResident heap row :=
  resident_edges heap facts.linked root available.resident row (by cbv; exact List.mem_cons_self)
private theorem allocated : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints inherited :=
  (SourceCurrentAllocatedPartialInitialization.operations_correct Cache.emptyState Cache.empty_valid).2.2
private theorem cache_valid : Cache.Valid before.checked.operations.constraints :=
  (SourceCurrentAllocatedPartialInitialization.operations_correct Cache.emptyState Cache.empty_valid).1.constraints

/-- Own cold calls publish both exact owners and leave exact full-state warm hits. -/
theorem constructed_owner_and_warm
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∃ (program : Syntax Symbol Guard) (value : Value Symbol Guard) (edge : EdgeValue Symbol Guard)
        (initial : Caller 8) (middle final : Caller 8) (constraint : Eq),
      InternedFreshOrdinaryConstruction.build program [] empty = .done value initial.checked.native.machine.heap ∧
      InternedRecordCoherence.Coherent initial.checked.native.machine.heap ∧
      Available initial.checked.native.machine.heap value ∧ EdgeResident initial.checked.native.machine.heap edge ∧
      SourceEqualityConstraintAllocation.Ready initial.checked.operations.constraints constraint ∧
      SourceCurrentAllocatedPartialWorker.nodeCall 4 4 4 4 4 4 4 4 4 32 0 ⟨constraint,value⟩ initial = .done value middle ∧
      beginNode ⟨constraint,value⟩ middle = (0,.ready value,middle) ∧
      SourceCurrentAllocatedPartialWorker.edgeCall 4 4 4 4 4 4 4 4 4 32 0 ⟨constraint,edge⟩ middle = .done edge final ∧
      beginEdge ⟨constraint,edge⟩ final = (0,.ready edge,final) ∧
      (∀ handle owner running, beginNode ⟨constraint,value⟩ initial = (handle,.evaluate owner,running) →
        owner = (⟨constraint,value⟩ : NodeRequest)) ∧
      (∀ handle owner running, beginEdge ⟨constraint,edge⟩ initial = (handle,.evaluate owner,running) →
        owner = (⟨constraint,edge⟩ : EdgeRequest)) := by
  refine ⟨expression,root,row,before,middle,after,inherited,built_done,facts.coherent,available,resident,allocated,
    ?_,?_,?_,?_,?_,?_⟩
  · cbv
  · cbv
  · cbv
  · cbv
  · intro handle owner running started
    exact SourceCurrentOuterKeyIdentity.node_evaluate_owner formulas solver nodeRequest before
      (SourceCurrentAllocatedPartialMemoSound.initial_sound formulas solver _ _ _) cache_valid facts.coherent
      allocated available handle owner running started
  · intro handle owner running started
    exact SourceCurrentOuterKeyIdentity.edge_evaluate_owner formulas solver edgeRequest before
      (SourceCurrentAllocatedPartialMemoSound.initial_sound formulas solver _ _ _) cache_valid facts.coherent
      allocated resident handle owner running started

private def honest : List SourceEqualityClassOrder.Record := [⟨.terminal,[[]]⟩]
private def altered : List SourceEqualityClassOrder.Record := [⟨.terminal,[]⟩]
private def storedPair := SourceEqualityConstraintAllocation.intern (some honest) Cache.emptyState
private def firstInherited := storedPair.1
private def secondInherited : Eq := .live 0 altered

/-- Stored alone permits different path metadata under the same actual interned key. -/
theorem stored_without_ready_is_not_injective :
    ∃ (cache : EqCache) (first second : NodeRequest),
      Cache.Valid cache ∧ InternedRecordCoherence.Coherent (empty : State Symbol Guard) ∧
      SourceEqualityConstraintAllocation.Stored cache first.inherited ∧
      SourceEqualityConstraintAllocation.Stored cache second.inherited ∧
      Available empty first.value ∧ Available empty second.value ∧ first.key = second.key ∧ first ≠ second := by
  refine ⟨storedPair.2,⟨firstInherited,.empty⟩,⟨secondInherited,.empty⟩,
    (SourceEqualityConstraintAllocation.intern_valid _ _ Cache.empty_valid).1,
    InternedNestedFacts.empty_facts.coherent,
    (SourceEqualityConstraintAllocation.intern_valid _ _ Cache.empty_valid).2,
    ?_,empty_available _,empty_available _,?_,?_⟩
  · exact (SourceEqualityConstraintAllocation.intern_valid (some honest) Cache.emptyState Cache.empty_valid).2
  · rfl
  · intro same
    have payloads := congrArg (fun request : NodeRequest => request.inherited.payload) same
    have lists : honest = altered := Option.some.inj payloads
    have paths := congrArg (fun records : List SourceEqualityClassOrder.Record => records.map (·.paths)) lists
    cases paths

end MicroCFTA.OuterKeyIdentityKernels

#check @MicroCFTA.OuterKeyIdentityKernels.constructed_owner_and_warm
#print axioms MicroCFTA.OuterKeyIdentityKernels.constructed_owner_and_warm
#check @MicroCFTA.OuterKeyIdentityKernels.stored_without_ready_is_not_injective
#print axioms MicroCFTA.OuterKeyIdentityKernels.stored_without_ready_is_not_injective
