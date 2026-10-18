import MicroCFTA.SourceCurrentClassPositionalFootprints
import MicroCFTA.SourceCurrentConjunctionClassHistoryEntry
set_option linter.all true
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.ClassFootprintCheck
noncomputable section
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceCurrentAllocatedSharedEditWorker
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Shared" => SourceCurrentAllocatedSharedTargetState.State
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq)
    (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)
private def plain : Guard := ⟨some [],.top⟩
private def leftPlan : Syntax Symbol Guard := .binder false (.node
  [.mk ("base",.top) plain [],.mk ("loop",.top) plain [.var 0],.mk ("left",.top) plain []])
private def rightPlan : Syntax Symbol Guard := .binder false (.node
  [.mk ("base",.top) plain [],.mk ("loop",.top) plain [.var 0],.mk ("right",.top) plain []])
private def tailPlan : Syntax Symbol Guard := .binder false (.node
  [.mk ("tail",.top) plain [],.mk ("repeat",.top) plain [.var 0]])
private def expression : Syntax Symbol Guard := .node [.mk ("roots",.top) plain [
  .node [.mk ("pair",.top) plain [leftPlan,tailPlan]],
  .node [.mk ("pair",.top) plain [rightPlan,tailPlan]]]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Node := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def values := children root
private def allocation := SourceEqualityConstraintAllocation.construct plain.equalities Cache.emptyState
private def allocated : SourceEqualityConstraintAllocation.Value := match allocation.1 with
  | .ok value => value | _ => .contradiction
private def before : SourceEqualityNativeDemand.State 10 :=
  ⟨initial 10 ⟨heap,Cache.emptyState⟩,SourceEqualityConstraintMemoAllocation.initial allocation.2⟩
private theorem built_done : built = .done root heap := by cbv
private theorem initial_ready : SourceCurrentConjunctionClassScan.Ready before := by
  have history : SourceEqualityOriginalAllocationHistory.History Cache.emptyState allocation.2 [plain] := by
    simpa only [List.nil_append] using SourceEqualityOriginalAllocationHistory.History.construct
      (.start Cache.emptyState) SourceEqualityGuardReadback.empty_cached
      (show allocation = (.ok allocated,allocation.2) by cbv)
  have covered : ∀ guard ∈ SourceEqualityConstraintOrigins.guards expression, guard ∈ [plain] := by
    intro guard member
    simp only [expression,leftPlan,rightPlan,tailPlan,SourceEqualityConstraintOrigins.guards,
      SourceEqualityConstraintOrigins.edgeGuards,SourceEqualityConstraintOrigins.childGuards,
      List.mem_append,List.mem_cons,List.not_mem_nil,List.nil_append,List.append_nil,or_false,or_self] at member ⊢
    exact member
  exact (SourceCurrentConjunctionClassHistoryEntry.constructed 10 history Cache.empty_valid
    expression covered root heap built_done).1
private def record : SourceEqualityClassOrder.Record :=
  (SourceEqualityClassOrder.recordOf [[0,0],[1,0]]).getD ⟨.empty,[]⟩
private theorem record_paths : record.paths = [[0,0],[1,0]] := by cbv
private theorem coherent : SourceEqualityClassOrder.Coherent record := by
  obtain ⟨actual,done,checked,_⟩ := SourceEqualityClassOrder.recordOf_complete [[0,0],[1,0]]
    ((EqualityTrie.toPathTrie_succeeds_iff _).mp
      ⟨.branch [(0,.branch [(0,.terminal)]),(1,.branch [(0,.terminal)])],by cbv⟩)
  have same : actual = record := Option.some.inj (done.symm.trans (by cbv))
  exact same ▸ checked
private theorem unselected : SourceCurrentClassPositionalFootprints.Unselected record 1 1 := by
  intro path member
  rw [record_paths] at member
  rcases List.mem_cons.mp member with rfl | member
  · unfold SourceEqualityEditCompiledPaths.Disjoint; decide
  · rcases List.mem_cons.mp member with rfl | member
    · unfold SourceEqualityEditCompiledPaths.Disjoint; decide
    · cases member
private def tail := SourceCurrentAllocatedClassWorker.runClass 8 16 32 16 16 256 record values before SourceCurrentMemoMergeGraph.empty
private def middleValues : List Node := match tail with | .done values .. => values | _ => []
private def head := SourceCurrentAllocatedClassWorker.runClass 8 16 32 16 16 256 record middleValues tail.state tail.memo
private def finalValues : List Node := match head with | .done values .. => values | _ => []
private def selected : Node := finalValues[1]?.getD .empty
private theorem tail_done : tail = .done middleValues tail.state tail.memo := by
  have tag : (match tail with | .done .. => true | _ => false) = true := by cbv
  cases found : tail <;> simp_all only [middleValues,SourceCurrentAllocatedClassWorker.Outcome.state,
    SourceCurrentAllocatedClassWorker.Outcome.memo,Bool.false_eq_true]
private theorem head_done : head = .done finalValues head.state head.memo := by
  have tag : (match head with | .done .. => true | _ => false) = true := by cbv
  cases found : head <;> simp_all only [finalValues,SourceCurrentAllocatedClassWorker.Outcome.state,
    SourceCurrentAllocatedClassWorker.Outcome.memo,Bool.false_eq_true]
private theorem selected_present : finalValues[1]? = some selected := by cbv
private theorem folded : SourceCurrentAllocatedClassWorker.fold 8 16 32 16 16 256 [record,record]
    values before SourceCurrentMemoMergeGraph.empty = .done finalValues head.state head.memo := by
  simp only [SourceCurrentAllocatedClassWorker.fold,SourceCurrentAllocatedClassWorker.Outcome.bind]
  rw [show SourceCurrentAllocatedClassWorker.runClass 8 16 32 16 16 256 record values before
    SourceCurrentMemoMergeGraph.empty = .done middleValues tail.state tail.memo from tail_done]
  exact head_done

private theorem witness :
    built = .done root heap ∧ SourceCurrentConjunctionClassScan.Ready before ∧
    record.paths = [[0,0],[1,0]] ∧ SourceCurrentClassPositionalFootprints.Unselected record 1 1 ∧
    SourceCurrentAllocatedClassWorker.fold 8 16 32 16 16 256 [record,record] values before
      SourceCurrentMemoMergeGraph.empty = .done finalValues head.state head.memo ∧
    ∃ entries, ∃ shared start finish : Shared 10, ∃ original childEntries,
      SourceCurrentAllocatedClassEditPlan.compiled record = .editBelow entries ∧
      shared.checked = head.state ∧ shared.memo = head.memo ∧ middleValues[1]? = some original ∧
      children (edit record middleValues 8 16 32 16 16 256) entries 0 (middleValues.take 1)
        (SourceCurrentAllocatedSharedTargetState.initial tail.state tail.memo) = .done (finalValues.take 1) start ∧
      children (edit record middleValues 8 16 32 16 16 256) entries 2 (middleValues.drop 2)
        finish = .done (finalValues.drop 2) shared ∧
      SourceEqualityNeededMap.lookup 1 entries = some (.editBelow childEntries) ∧
      SourceEqualityNeededMap.lookup 1 childEntries = none ∧
      edit record middleValues 8 16 32 16 16 256 (.editBelow childEntries) original start = .done selected finish ∧
      0 < start.checked.native.nodes.next := by
  refine ⟨built_done,initial_ready,record_paths,unselected,folded,?_⟩
  obtain ⟨entries,shared,start,finish,original,built,checked,memo,source,earlier,later,dispatch⟩ :=
    SourceCurrentClassPositionalFootprints.class_dispatch head_done coherent 1 1 unselected selected_present
  rcases dispatch with absent | ⟨childEntries,found,none,actual⟩
  · have selected : ∃ child, SourceEqualityNeededMap.lookup 1 entries = some child := by
      have same : entries = [(0,.editBelow [(0,.editAt [0,0])]),(1,.editBelow [(0,.editAt [1,0])])] := by
        have exactBuild : SourceCurrentAllocatedClassEditPlan.compiled record =
          .editBelow [(0,.editBelow [(0,.editAt [0,0])]),(1,.editBelow [(0,.editAt [1,0])])] := by cbv
        exact SourceEqualityEdits.Edits.editBelow.inj (built.symm.trans exactBuild)
      rw [same]
      exact ⟨_,rfl⟩
    obtain ⟨child,found⟩ := selected
    have missing : SourceEqualityNeededMap.lookup 1 entries = none := by simpa using absent.1
    rw [missing] at found
    cases found
  · refine ⟨entries,shared,start,finish,original,childEntries,built,checked,memo,source,earlier,later,found,none,actual,?_⟩
    have earlierCall := earlier
    have expected : start = (children (edit record middleValues 8 16 32 16 16 256) entries 0
        (middleValues.take 1) (SourceCurrentAllocatedSharedTargetState.initial tail.state tail.memo)).state :=
      (congrArg Outcome.state earlierCall).symm
    rw [expected]
    have same : entries = [(0,.editBelow [(0,.editAt [0,0])]),(1,.editBelow [(0,.editAt [1,0])])] := by
      have exactBuild : SourceCurrentAllocatedClassEditPlan.compiled record =
          .editBelow [(0,.editBelow [(0,.editAt [0,0])]),(1,.editBelow [(0,.editAt [1,0])])] := by cbv
      exact SourceEqualityEdits.Edits.editBelow.inj (built.symm.trans exactBuild)
    rw [same]
    cbv

/-- Repeated actual classes retain the second-child footprint at the captured second forest call. -/
theorem repeated_class_dispatch :
    built = .done root heap ∧ SourceCurrentConjunctionClassScan.Ready before ∧
    record.paths = [[0,0],[1,0]] ∧ SourceCurrentClassPositionalFootprints.Unselected record 1 1 ∧
    SourceCurrentAllocatedClassWorker.fold 8 16 32 16 16 256 [record,record] values before
      SourceCurrentMemoMergeGraph.empty = .done finalValues head.state head.memo ∧
    ∃ entries, ∃ shared start finish : Shared 10, ∃ original childEntries,
      SourceCurrentAllocatedClassEditPlan.compiled record = .editBelow entries ∧
      shared.checked = head.state ∧ shared.memo = head.memo ∧ middleValues[1]? = some original ∧
      children (edit record middleValues 8 16 32 16 16 256) entries 0 (middleValues.take 1)
        (SourceCurrentAllocatedSharedTargetState.initial tail.state tail.memo) = .done (finalValues.take 1) start ∧
      children (edit record middleValues 8 16 32 16 16 256) entries 2 (middleValues.drop 2)
        finish = .done (finalValues.drop 2) shared ∧
      SourceEqualityNeededMap.lookup 1 entries = some (.editBelow childEntries) ∧
      SourceEqualityNeededMap.lookup 1 childEntries = none ∧
      edit record middleValues 8 16 32 16 16 256 (.editBelow childEntries) original start = .done selected finish ∧
      0 < start.checked.native.nodes.next := witness

end
end MicroCFTA.ClassFootprintCheck
