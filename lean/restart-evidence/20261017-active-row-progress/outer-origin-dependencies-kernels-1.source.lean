import MicroCFTA.SourceCurrentOuterOriginDependencies
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
namespace MicroCFTA.OuterOriginDependenciesIntegration
open EqualityNormalize SourceEqualityClassOrder SourceEqualityDescend
open SourceEqualityConstraintAllocation
local notation "Operations" => SourceEqualityConstraintMemoAllocation.State
private def leftPaths : Class := [[0,0],[0,1]]
private def rightPaths : Class := [[0,0,0],[0,0,1]]
private def sourceRecord (paths : Class) : Record := (recordOf paths).getD ⟨.empty,[]⟩
private def first : Value := .live 0 [sourceRecord leftPaths]
private def firstState := (construct (some [leftPaths]) Cache.emptyState).2
private def second : Value := .live 1 [sourceRecord rightPaths]
private def secondState := (construct (some [rightPaths]) firstState).2
private def before : Operations := SourceEqualityConstraintMemoAllocation.initial secondState
private theorem first_cached : SourceEqualityGuardReadback.Cached (some [leftPaths]) := by
  intro classes same
  cases same
  exact SourceEqualityGuardReadback.normalized (show mkEqConstraints 2 [leftPaths] = .normalized [leftPaths] by cbv)
private theorem second_cached : SourceEqualityGuardReadback.Cached (some [rightPaths]) := by
  intro classes same
  cases same
  exact SourceEqualityGuardReadback.normalized (show mkEqConstraints 2 [rightPaths] = .normalized [rightPaths] by cbv)
private theorem initial : SourceEqualityConstraintMemoAllocation.Valid before ∧
    Ready before.constraints first ∧ Ready before.constraints second := by
  obtain ⟨firstValue, cache1, actual1, valid1, ready1, steps1, read1, classes1⟩ :=
    construct_complete (some [leftPaths]) first_cached Cache.emptyState Cache.empty_valid
  have done1 : construct (some [leftPaths]) Cache.emptyState = (.ok first,firstState) := by cbv
  rw [done1] at actual1
  cases actual1
  obtain ⟨secondValue, cache2, actual2, valid2, ready2, steps2, read2, classes2⟩ :=
    construct_complete (some [rightPaths]) second_cached firstState valid1
  have done2 : construct (some [rightPaths]) firstState = (.ok second,secondState) := by cbv
  rw [done2] at actual2
  cases actual2
  exact ⟨SourceEqualityConstraintMemoAllocation.initial_valid _ valid2,
    ready1.grows (Cache.steps_table_extends steps2),ready2⟩
private def model : Language.Term Unit := .node ()
  [.node () [.node () [.node () [],.node () []],.node () [.node () [],.node () []]],
   .node () [.node () [.node () [],.node () []],.node () [.node () [],.node () []]]]
private theorem first_satisfied : SourceEqualityPrecheck.Sat model first.payload := by cbv
private theorem second_satisfied : SourceEqualityPrecheck.Sat model second.payload := by cbv
/-- Actual source allocation and combination carry an original dependency into the literal live child, including a warm combination replay. -/
theorem original_dependency_in_actual_child :
    ∃ combined outputs leftRecord rightRecord leftChild rightChild,
      SourceEqualityConstraintMemoAllocation.Valid before ∧
      Ready before.constraints first ∧ Ready before.constraints second ∧
      (SourceEqualityConstraintMemoAllocation.combine first second before).1 = .ok combined ∧
      combined.payload = some outputs ∧ leftRecord ∈ outputs ∧ rightRecord ∈ outputs ∧
      leftRecord ≠ rightRecord ∧ Subsumes leftRecord.paths rightRecord.paths ∧
      record 0 leftRecord = some leftChild ∧ record 0 rightRecord = some rightChild ∧
      leftChild ∈ records 0 outputs ∧ rightChild ∈ records 0 outputs ∧
      leftChild ≠ rightChild ∧ Subsumes leftChild.paths rightChild.paths ∧
      let middle := (SourceEqualityConstraintMemoAllocation.combine first second before).2
      let child := SourceEqualityConstraintMemoAllocation.descend combined 0 middle
      child.1.payload = some (records 0 outputs) ∧
      SourceEqualityConstraintMemoAllocation.Valid child.2 ∧ Ready child.2.constraints child.1 ∧
      SourceCurrentEqualityOperationFixed.FixedPayload child.1.payload ∧
      SourceEqualityConstraintMemoAllocation.combine first second middle = (.ok combined,middle) := by
  obtain ⟨combined, actual, validMiddle, readyMiddle, growth, dependencies⟩ :=
    SourceCurrentOuterOriginDependencies.combine_descend_dependencies first second before initial.1 initial.2.1 initial.2.2
  obtain ⟨other, otherActual, _, _, payload, _⟩ :=
    SourceEqualityConstraintMemoAllocation.combine_correct first second before initial.1 initial.2.1 initial.2.2
  have same : other = combined := Except.ok.inj (otherActual.symm.trans actual)
  subst other
  have satisfied := ((SourceEqualityInheritedPayload.combine_exact (Symbol := Unit) payload).2 model).mpr
    ⟨first_satisfied,second_satisfied⟩
  cases combined with
  | contradiction => cases satisfied
  | live identity outputs =>
      have originsLeft : leftPaths ∈ ((SourceEqualityInheritedPayload.classes first.payload).getD [] ++
          (SourceEqualityInheritedPayload.classes second.payload).getD []) := by cbv
      have originsRight : rightPaths ∈ ((SourceEqualityInheritedPayload.classes first.payload).getD [] ++
          (SourceEqualityInheritedPayload.classes second.payload).getD []) := by cbv
      have relation : Subsumes leftPaths rightPaths :=
        ⟨[0,0],by decide,[0,0,0],by decide,⟨[0],rfl⟩,by decide⟩
      obtain ⟨leftRecord,leftKnown,rightRecord,rightKnown,leftIncluded,rightIncluded,different,dependency,children⟩ :=
        dependencies outputs rfl leftPaths originsLeft rightPaths originsRight relation
      have known := readyMiddle.2 outputs rfl leftRecord leftKnown
      obtain ⟨leftChild,leftRead⟩ := SourceCurrentEqualityDescendFixed.record_retained 0 leftRecord known.1
        [0] [1] (leftIncluded [0,0] (by decide)) (leftIncluded [0,1] (by decide)) (by decide)
      obtain ⟨childValid,childReady,_,childFixed,childPayload,leftPresent,rightChild,rightPresent,rightRead,childDifferent,childDependency⟩ :=
        children 0 leftChild leftRead
      refine ⟨.live identity outputs,outputs,leftRecord,rightRecord,leftChild,rightChild,
        initial.1,initial.2.1,initial.2.2,actual,rfl,leftKnown,rightKnown,different,dependency,leftRead,rightRead,
        leftPresent,rightPresent,childDifferent,childDependency,childPayload,childValid,childReady,childFixed,?_⟩
      exact SourceEqualityConstraintMemoAllocation.combine_replay first second before (.live identity outputs) actual
end MicroCFTA.OuterOriginDependenciesIntegration
#check @MicroCFTA.OuterOriginDependenciesIntegration.original_dependency_in_actual_child
#print axioms MicroCFTA.OuterOriginDependenciesIntegration.original_dependency_in_actual_child
