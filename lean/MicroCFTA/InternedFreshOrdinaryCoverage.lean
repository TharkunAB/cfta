import MicroCFTA.InternedFreshOrdinaryGrowth
import MicroCFTA.InternedNestedCoverage

/-!
# Payload coverage through completed repaired nested construction

The repaired scheduler retains every earlier pending-key permission.
A completed binder installs its own payload and removes its permission.
The proof covers arbitrary nested syntax and all captured values. It does
not assume that a requested binder completes.
-/
namespace MicroCFTA.InternedFreshOrdinaryCoverage
open Cache InternedConstructorTemplates InternedRecordCoherence
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work request work_correct bind_correct)
open InternedNestedCoverage (OnDone bind_covered work_covered request_covered)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryGrowth
open InternedBinderProtocol (NodeKey Reference)

mutual
/-- Every successful nested expression retains coverage for arbitrary earlier pending binders. -/
theorem build_covered [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (valid : InternedConstructorTemplates.Valid state) (covered : Covered pending state) :
    OnDone pending (build expression environment state) := by
  cases expression with
  | empty | var index =>
      intro value after returned
      simp only [build, Outcome.done.injEq] at returned
      rcases returned with ⟨_, rfl⟩
      exact covered
  | node edges =>
      rw [build]
      apply bind_covered pending pending _ _ (buildEdges_covered edges environment state valid covered)
      intro values after returned coverage
      have afterValid : InternedConstructorTemplates.Valid after := by
        simpa [returned, Outcome.state] using (buildEdges_correct edges environment state valid).1
      exact work_covered (makeNode values) after afterValid coverage
  | union members =>
      rw [build]
      apply bind_covered pending pending _ _ (buildMany_covered members environment state valid covered)
      intro values after returned coverage
      have afterValid : InternedConstructorTemplates.Valid after := by
        simpa [returned, Outcome.state] using (buildMany_correct members environment state valid).1
      exact work_covered (makeUnion values) after afterValid coverage
  | binder smart body =>
      let callback := fun name current => (build body (.reference name :: environment) current).bind
        fun value next => work (withoutSelfReference name value) next
      have callbackCovered : ∀ keys name current, InternedConstructorTemplates.Valid current → Covered keys current →
          OnDone keys (callback name current) := by
        intro keys name current currentValid coverage
        apply bind_covered keys keys _ _ (build_covered body _ current currentValid coverage)
        intro value after returned afterCoverage
        have afterValid : InternedConstructorTemplates.Valid after := by
          simpa [returned, Outcome.state] using (build_correct body (.reference name :: environment) current currentValid).1
        exact work_covered (withoutSelfReference name value) after afterValid afterCoverage
      have callbackValid : ∀ name current, InternedConstructorTemplates.Valid current →
          InternedConstructorTemplates.Valid (callback name current).state := by
        intro name current currentValid
        exact (InternedNestedConstruction.bind_correct _ _ current (build_correct body _ current currentValid)
          (fun value next nextValid => work_correct (withoutSelfReference name value) next nextValid)).1
      rw [build]
      change OnDone pending ((callback .depth state).bind fun depth afterDepth =>
        (callback (.uninterned (ordinaryLevel depth)) afterDepth).bind fun ordinary afterOrdinary =>
          request smart depth ordinary callback afterOrdinary)
      apply bind_covered pending pending _ _ (callbackCovered pending .depth state valid covered)
      intro depth afterDepth depthReturned depthCoverage
      have depthValid : InternedConstructorTemplates.Valid afterDepth := by
        simpa [depthReturned, Outcome.state] using callbackValid .depth state valid
      apply bind_covered pending pending _ _
        (callbackCovered pending (.uninterned (ordinaryLevel depth)) afterDepth depthValid depthCoverage)
      intro ordinary afterOrdinary ordinaryReturned ordinaryCoverage
      have ordinaryValid : InternedConstructorTemplates.Valid afterOrdinary := by
        simpa [ordinaryReturned, Outcome.state] using callbackValid (.uninterned (ordinaryLevel depth)) afterDepth depthValid
      exact request_covered smart depth ordinary callback afterOrdinary ordinaryValid ordinaryCoverage callbackCovered
termination_by sizeOf expression

/-- Successful child traversal restores the exact incoming pending-key allowance. -/
theorem buildMany_covered [DecidableEq (EdgeKey Symbol Guard)] (expression : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (valid : InternedConstructorTemplates.Valid state) (covered : Covered pending state) :
    OnDone pending (buildMany expression environment state) := by
  cases expression with
  | nil =>
      intro value after returned
      simp only [buildMany] at returned
      cases returned
      exact covered
  | cons first rest =>
      rw [buildMany]
      apply bind_covered pending pending _ _ (build_covered first environment state valid covered)
      intro value afterHead headReturned headCoverage
      have headValid : InternedConstructorTemplates.Valid afterHead := by
        simpa [headReturned, Outcome.state] using (build_correct first environment state valid).1
      apply bind_covered pending pending _ _ (buildMany_covered rest environment afterHead headValid headCoverage)
      intro values afterTail _ tailCoverage
      intro result final returned
      cases returned
      exact tailCoverage
termination_by sizeOf expression

/-- Separate edge interning preserves the pending-key allowance between nested siblings. -/
theorem buildEdges_covered [DecidableEq (EdgeKey Symbol Guard)] (expression : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (valid : InternedConstructorTemplates.Valid state) (covered : Covered pending state) :
    OnDone pending (buildEdges expression environment state) := by
  cases expression with
  | nil =>
      intro value after returned
      simp only [buildEdges] at returned
      cases returned
      exact covered
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          rw [buildEdges]
          apply bind_covered pending pending _ _ (buildMany_covered children environment state valid covered)
          intro values afterChildren childrenReturned childrenCoverage
          have childrenValid : InternedConstructorTemplates.Valid afterChildren := by
            simpa [childrenReturned, Outcome.state] using (buildMany_correct children environment state valid).1
          apply bind_covered pending pending _ _ (work_covered (makeEdge symbol constraint values) afterChildren childrenValid childrenCoverage)
          intro edge afterEdge edgeReturned edgeCoverage
          have edgeValid : InternedConstructorTemplates.Valid afterEdge := by
            simpa [edgeReturned, Outcome.state] using (work_correct (makeEdge symbol constraint values) afterChildren childrenValid).1
          apply bind_covered pending pending _ _ (buildEdges_covered rest environment afterEdge edgeValid edgeCoverage)
          intro edges afterTail _ tailCoverage
          intro result final returned
          cases returned
          exact tailCoverage
termination_by sizeOf expression
end

/-- Every completed empty-table run has a payload for each installed identity. -/
theorem closed_covered [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (value : Value Symbol Guard) (state : State Symbol Guard)
    (completed : build expression [] empty = .done value state) : Covered [] state :=
  build_covered expression [] empty empty_valid empty_correct.2 value state completed

end MicroCFTA.InternedFreshOrdinaryCoverage
