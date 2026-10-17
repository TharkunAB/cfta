import MicroCFTA.InternedFreshOrdinaryResultMass
import MicroCFTA.InternedFreshOrdinaryReplay

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 2000000

namespace MicroCFTA.ResultMassIntegration
open Cache InternedConstructorTemplates
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction
open InternedFreshOrdinaryResultMass
local notation "Stored" => InternedValueMassHeap.Stored
local notation "mass" => InternedValueMass.value

private def fixture : Syntax Nat Bool :=
  .binder false (.node [.mk 7 false [.var 0,
    .binder false (.union [.var 0, .node [.mk 8 true [.var 1]]])]])

/-- An actual nested capture, union, and both Mu probes produce their own complete causal mass store. -/
theorem constructed_nested :
    ∃ value after,
      build fixture [] empty = .done value after ∧
      Stored (transform fixture 1) after ∧ mass value ≤ transform fixture 1 ∧
      (match value with | .mu _ _ _ _ => True | _ => False) := by
  have finished : (match build fixture [] empty with | .done _ _ => true | .pending _ _ => false) = true := by
    decide +kernel
  have shape : match build fixture [] empty with
      | .done (.mu _ _ _ _) _ => True
      | _ => False := by decide +kernel
  have checked := build_bound fixture [] empty 1 (InternedValueMassHeap.empty_stored (by omega))
    (by intro value member; cases member)
  cases actual : build fixture [] empty with
  | pending key after => simp only [actual, Bool.false_eq_true] at finished
  | done value after =>
      have stored : Stored (transform fixture 1) after := by
        simpa only [actual, Outcome.state] using checked.1
      have bounded := checked.2 value after actual
      have mu : match value with | .mu _ _ _ _ => True | _ => False := by
        simpa only [actual] using shape
      exact ⟨value, after, rfl, stored, bounded, mu⟩

/-- The same completed first-writer state supports exact warm replay and a second independently derived result bound. -/
theorem actual_warm_replay :
    ∃ value after,
      build fixture [] empty = .done value after ∧
      build fixture [] after = .done value after ∧
      Stored (transform fixture 1) after ∧
      Stored (transform fixture (transform fixture 1)) after ∧
      mass value ≤ transform fixture 1 ∧ mass value ≤ transform fixture (transform fixture 1) := by
  obtain ⟨value, after, completed, stored, bounded, _mu⟩ := constructed_nested
  have replay := InternedFreshOrdinaryReplay.empty_replay fixture value after after completed (grows_refl _)
  have second := build_bound fixture [] after (transform fixture 1) stored (by intro value member; cases member)
  refine ⟨value, after, completed, replay, stored, ?_, bounded, second.2 value after replay⟩
  simpa only [replay, Outcome.state] using second.1

private def reservedKey : InternedBinderProtocol.NodeKey :=
  muKey (Value.reference .depth : Value Nat Bool) (.reference (.uninterned 0))

private def reservedHeap : State Nat Bool :=
  {empty with nodes := (Cache.intern (empty (Symbol := Nat) (Guard := Bool)).nodes reservedKey).2}

/-- A literal pending owner retains a produced all-outcome store bound without a completed payload. -/
theorem pending_store :
    build (.binder false (.var 0)) [] reservedHeap = .pending reservedKey reservedHeap ∧
      Stored 1 reservedHeap ∧ Stored (transform (.binder false (.var 0) : Syntax Nat Bool) 1) reservedHeap := by
  have stored : Stored 1 reservedHeap :=
    (InternedValueMassHeap.empty_stored (Symbol := Nat) (Guard := Bool) (by omega)).node_cache _
  have actual : build (.binder false (.var 0)) [] reservedHeap = .pending reservedKey reservedHeap := by
    simp only [build, Outcome.bind, InternedNestedConstruction.work, withoutSelfReference]
    rfl
  have produced := build_bound (.binder false (.var 0)) [] reservedHeap 1 stored (by intro value member; cases member)
  exact ⟨actual, stored, by simpa only [actual, Outcome.state] using produced.1⟩

end MicroCFTA.ResultMassIntegration

#print axioms MicroCFTA.ResultMassIntegration.constructed_nested
#check @MicroCFTA.ResultMassIntegration.constructed_nested
#print axioms MicroCFTA.ResultMassIntegration.actual_warm_replay
#check @MicroCFTA.ResultMassIntegration.actual_warm_replay
#print axioms MicroCFTA.ResultMassIntegration.pending_store
#check @MicroCFTA.ResultMassIntegration.pending_store
