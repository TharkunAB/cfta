import MicroCFTA.SourceCurrentOuterInheritedDescent
import MicroCFTA.SourceEqualityRequiredCache

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000

namespace MicroCFTA.OuterInheritedDescentKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open SourceCurrentAllocatedPartialState
open SourceCurrentOuterInheritedDescent
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Guard
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Operations" => SourceEqualityConstraintMemoAllocation.State
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq)
    (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)

private def plain : Guard := ⟨some [],.top⟩
private def expression : Syntax Symbol Guard :=
  .node [.mk ("root",.top) plain [.binder false (.node [.mk ("step",.top) plain [.var 0]])]]
private def built := build expression [] empty
private def value : Node := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private theorem built_done : built = .done value heap := by cbv
private theorem heap_ready : SourceEqualityRequiredCache.Ready heap :=
  SourceEqualityRequiredCache.constructed expression value heap built_done
private theorem value_available : Available heap value :=
  (InternedFreshOrdinaryFacts.closed_verified expression).result value heap built_done

private def record : SourceEqualityClassOrder.Record :=
  (SourceEqualityClassOrder.recordOf [[0,0],[0,1]]).getD ⟨.empty,[]⟩
private def allocated := SourceEqualityConstraintAllocation.intern (some [record]) Cache.emptyState
private def inherited := allocated.1
private def operations : Operations := SourceEqualityConstraintMemoAllocation.initial allocated.2
private theorem wellFormed : SourceEqualityDescend.WellFormed (some [record]) := by
  intro records same current member
  cases same
  have selected : current = record := by simpa only [List.mem_singleton] using member
  subst current
  have built : SourceEqualityClassOrder.recordOf [[0,0],[0,1]] = some record := by cbv
  obtain ⟨original,actual,coherent,_paths⟩ :=
    SourceEqualityClassOrder.recordOf_complete [[0,0],[0,1]] (by unfold EqualityTrie.Supported; decide)
  have same : original = record := Option.some.inj (actual.symm.trans built)
  subst original
  refine ⟨coherent,SourceEqualityDescend.recordOf_ascending _ _ built,?_⟩
  have fields : record.paths = [[0,0],[0,1]] := by cbv
  rw [fields]
  exact ⟨[0,0],by decide,[0,1],by decide,by decide⟩
private theorem operations_valid : SourceEqualityConstraintMemoAllocation.Valid operations :=
  SourceEqualityConstraintMemoAllocation.initial_valid _
    (SourceEqualityConstraintAllocation.intern_valid (some [record]) Cache.emptyState Cache.empty_valid).1
private theorem inherited_ready : SourceEqualityConstraintAllocation.Ready operations.constraints inherited :=
  SourceEqualityConstraintAllocation.intern_ready (some [record]) Cache.emptyState Cache.empty_valid wellFormed
private theorem inherited_literal : inherited = .live 0 [record] := by cbv
private def caller : State 8 := initial
  ⟨SourceRecursiveIntersectionThunks.initial 8 ⟨heap,Cache.emptyState⟩,operations⟩
  SourceCurrentMemoMergeGraph.empty SourceCurrentEmptinessMemo.empty
private def request : NodeRequest := ⟨inherited,value⟩
private def parentStarted := beginNode request caller
private def running := parentStarted.2.2
private def descended := SourceCurrentAllocatedPartialGraph.descend running inherited 0
private def child : NodeRequest := ⟨descended.1,value⟩
private def childStarted := beginNode child descended.2
private def secondRunning := childStarted.2.2
private def warm := SourceCurrentAllocatedPartialGraph.descend secondRunning inherited 0
private def last := SourceEqualityConstraintMemoAllocation.descend descended.1 0 warm.2.checked.operations

/-- Actual inherited descent changes the key of the same source value while its earlier owner evaluates. -/
theorem actual_cold_warm_descent :
    build expression [] empty = .done value heap ∧ SourceEqualityRequiredCache.Ready heap ∧
    Available heap value ∧ value.free = [] ∧
    SourceEqualityConstraintMemoAllocation.Valid operations ∧
    SourceEqualityConstraintAllocation.Ready operations.constraints inherited ∧
    pathHeight inherited = 2 ∧ pathHeight descended.1 = 1 ∧
    pathHeight descended.1 < pathHeight inherited ∧ child.value = request.value ∧
    child.key ≠ request.key ∧
    parentStarted.2.1 = .evaluate request ∧
    childStarted.2.1 = .evaluate child ∧
    secondRunning.nodeResults.cells 0 = some ⟨request,.evaluating⟩ ∧
    secondRunning.nodeResults.cells 1 = some ⟨child,.evaluating⟩ ∧
    warm = (descended.1,secondRunning) := by
  have nonempty : [record] ≠ [] := List.cons_ne_nil _ _
  have namedReady : SourceEqualityConstraintAllocation.Ready operations.constraints (.live 0 [record]) :=
    inherited_literal ▸ inherited_ready
  have strict : pathHeight descended.1 < pathHeight inherited := by
    change pathHeight (SourceEqualityConstraintMemoAllocation.descend inherited 0 operations).1 < pathHeight inherited
    rw [inherited_literal]
    exact descend_lt 0 [record] 0 operations operations_valid namedReady nonempty
  have separate : child.key ≠ request.key := by
    simpa only [child,request,descended,SourceCurrentAllocatedPartialGraph.descend,
      SourceCurrentAllocatedPartialState.advance,SourceCurrentAllocatedQueryMemo.advancePhysical,
      running,parentStarted,beginNode,caller,initial,FlatMemoThunk.lookupOrInsert,FlatMemoThunk.empty,
      FlatMemoThunk.demand,inherited_literal] using
      node_key_ne 0 [record] 0 operations operations_valid namedReady nonempty value
  refine ⟨built_done,heap_ready,value_available,?_,operations_valid,inherited_ready,?_,?_,strict,rfl,separate,?_,?_,?_,?_,?_⟩
  all_goals cbv

/-- Empty inherited payloads keep their actual identity and do not supply strict descent. -/
theorem empty_inherited_fixed :
    pathHeight last.1 = 0 ∧
    (∃ identity, last.1 = .live identity []) ∧
    SourceEqualityConstraintMemoAllocation.descend last.1 0 last.2 = (last.1,last.2) ∧
    SourceEqualityConstraintMemoAllocation.descend last.1 19 last.2 = (last.1,last.2) := by
  refine ⟨?_,?_,?_,?_⟩
  · cbv
  · exact ⟨2,by cbv⟩
  · cbv
  · cbv

end MicroCFTA.OuterInheritedDescentKernels
