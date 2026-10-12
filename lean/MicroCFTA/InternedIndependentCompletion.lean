import MicroCFTA.InternedNestedSpecialization
import MicroCFTA.InternedNestedCoverage

/-!
# First-run completion from lexical independence of nested binders

The first depth probe completes by structural induction. Its actual trace
supplies the ordinary template for both later callbacks. Those callbacks
can execute with an unfinished enclosing binder because ordinary work does
not read a Mu payload. No completed first execution is assumed.
-/
namespace MicroCFTA.InternedIndependentCompletion
open InternedConstructorTemplates InternedNestedConstruction InternedRecordCoherence
open InternedNestedSpecialization InternedNestedCoverage
open InternedBinderProtocol (Reference)

mutual
/-- Each binder's nested dependencies ignore that binder's local argument. -/
def Staged : Syntax Symbol Guard → Prop
  | .empty | .var _ => True
  | .node edges => EdgesStaged edges
  | .union members => ManyStaged members
  | .binder _ body => Independent body ∧ Staged body
termination_by expression => sizeOf expression

/-- Ordered child expressions satisfy the same source dependency condition. -/
def ManyStaged : List (Syntax Symbol Guard) → Prop
  | [] => True
  | first :: rest => Staged first ∧ ManyStaged rest
termination_by expressions => sizeOf expressions

/-- Every edge child satisfies the source dependency condition. -/
def EdgesStaged : List (EdgeSyntax Symbol Guard) → Prop
  | [] => True
  | .mk _ _ children :: rest => ManyStaged children ∧ EdgesStaged rest
termination_by expressions => sizeOf expressions
end

mutual
/-- Source-derived dependency independence excludes pending readback on the first execution. -/
theorem build_completes [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (staged : Staged expression) (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (valid : InternedConstructorTemplates.Valid state) (covered : Covered [] state) :
    ∃ value final, build expression environment state = .done value final := by
  cases expression with
  | empty => exact ⟨.empty, state, by simp only [build]⟩
  | var index => exact ⟨environment[index]?.getD .empty, state, by simp only [build]⟩
  | node edges =>
      simp only [Staged] at staged
      obtain ⟨values, after, completed⟩ := buildEdges_completes edges staged environment state valid covered
      simp only [build, completed, Outcome.bind, work]
      exact ⟨_, _, rfl⟩
  | union members =>
      simp only [Staged] at staged
      obtain ⟨values, after, completed⟩ := buildMany_completes members staged environment state valid covered
      simp only [build, completed, Outcome.bind, work]
      exact ⟨_, _, rfl⟩
  | binder smart body =>
      simp only [Staged] at staged
      let callback := fun name current => (build body (.reference name :: environment) current).bind
        fun value next => work (withoutSelfReference name value) next
      obtain ⟨initial, afterInitial, initialDone⟩ :=
        build_completes body staged.2 (.reference .depth :: environment) state valid covered
      have initialFacts := build_correct body (.reference .depth :: environment) state valid
      rw [initialDone] at initialFacts
      have initialCovered := build_covered body (.reference .depth :: environment) state valid covered _ _ initialDone
      obtain ⟨template, specialize⟩ := build_specializes body staged.1 (.reference .depth) environment state
        initial afterInitial valid initialDone
      have callbackTemplate : ∀ name after, InternedConstructorTemplates.Valid after → Grows afterInitial after →
          callback name after = work (compileBody template name) after := by
        intro name after afterValid growth
        simp only [callback, specialize (.reference name) after afterValid growth, compileBody, work_bind]
      let depthResult := run (withoutSelfReference .depth initial) afterInitial
      have depthDone : callback .depth state = .done depthResult.1 depthResult.2 := by
        simp only [callback, initialDone, Outcome.bind, work, depthResult]
      have depthFacts := run_correct (withoutSelfReference .depth initial) afterInitial initialFacts.1
      have depthCovered := run_covered (withoutSelfReference .depth initial) afterInitial initialFacts.1 initialCovered
      let ordinaryResult := run (compileBody template (.uninterned depthResult.1.depth)) depthResult.2
      have ordinaryDone : callback (.uninterned depthResult.1.depth) depthResult.2 =
          .done ordinaryResult.1 ordinaryResult.2 := by
        exact callbackTemplate _ _ depthFacts.1 depthFacts.2
      have ordinaryFacts := run_correct (compileBody template (.uninterned depthResult.1.depth)) depthResult.2 depthFacts.1
      have ordinaryCovered := run_covered (compileBody template (.uninterned depthResult.1.depth))
        depthResult.2 depthFacts.1 depthCovered
      have expanded : build (.binder smart body) environment state =
          (callback .depth state).bind fun depth afterDepth =>
            (callback (.uninterned depth.depth) afterDepth).bind fun ordinary afterOrdinary =>
              request smart depth ordinary callback afterOrdinary := by rw [build]
      rw [expanded, depthDone]
      simp only [Outcome.bind]
      rw [ordinaryDone]
      cases present : ordinaryResult.2.nodes.table (muKey depthResult.1 ordinaryResult.1) with
      | some entry =>
          rcases ordinaryCovered.nodes _ entry present with impossible | ⟨record, stored⟩
          · cases impossible
          · change ordinaryResult.2.nodeRecords (muKey depthResult.1 ordinaryResult.1) = some record at stored
            simp only [request, present, stored]
            exact ⟨_, _, rfl⟩
      | none =>
          let key := muKey depthResult.1 ordinaryResult.1
          let entry := Cache.intern ordinaryResult.2.nodes key
          let allocated := {ordinaryResult.2 with nodes := entry.2}
          have allocatedValid : InternedConstructorTemplates.Valid allocated :=
            ⟨ordinaryFacts.1.1, (Cache.intern_correct _ _ ordinaryFacts.1.2).1⟩
          have allocatedGrowth : Grows ordinaryResult.2 allocated :=
            ⟨Cache.extends_refl _, InternedBinderProtocol.intern_grows _ _, Cache.extends_refl _, Cache.extends_refl _⟩
          have actualDone := callbackTemplate (.interned entry.1.identity) allocated allocatedValid
            (grows_trans depthFacts.2 (grows_trans ordinaryFacts.2 allocatedGrowth))
          simp only [request, present]
          change ∃ value final, (callback (.interned entry.1.identity) allocated).bind _ = .done value final
          rw [actualDone]
          simp only [work, Outcome.bind]
          exact ⟨_, _, rfl⟩
termination_by sizeOf expression

/-- The first execution of every ordered child completes before its next sibling runs. -/
theorem buildMany_completes [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (staged : ManyStaged expressions) (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (valid : InternedConstructorTemplates.Valid state) (covered : Covered [] state) :
    ∃ values final, buildMany expressions environment state = .done values final := by
  cases expressions with
  | nil => exact ⟨[], state, by simp only [buildMany]⟩
  | cons first rest =>
      simp only [ManyStaged] at staged
      obtain ⟨value, afterHead, headDone⟩ := build_completes first staged.1 environment state valid covered
      have headFacts := build_correct first environment state valid
      rw [headDone] at headFacts
      have headCovered := build_covered first environment state valid covered value afterHead headDone
      obtain ⟨values, final, tailDone⟩ := buildMany_completes rest staged.2 environment afterHead headFacts.1 headCovered
      exact ⟨value :: values, final, by simp only [buildMany, headDone, tailDone, Outcome.bind]⟩
termination_by sizeOf expressions

/-- First-run completion includes each child, each actual edge request, and the remaining edges. -/
theorem buildEdges_completes [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (staged : EdgesStaged expressions) (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (valid : InternedConstructorTemplates.Valid state) (covered : Covered [] state) :
    ∃ values final, buildEdges expressions environment state = .done values final := by
  cases expressions with
  | nil => exact ⟨[], state, by simp only [buildEdges]⟩
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          simp only [EdgesStaged] at staged
          obtain ⟨values, afterChildren, childrenDone⟩ :=
            buildMany_completes children staged.1 environment state valid covered
          have childrenFacts := buildMany_correct children environment state valid
          rw [childrenDone] at childrenFacts
          have childrenCovered := buildMany_covered children environment state valid covered _ _ childrenDone
          let edgeResult := run (makeEdge symbol constraint values) afterChildren
          have edgeFacts := run_correct (makeEdge symbol constraint values) afterChildren childrenFacts.1
          have edgeCovered := run_covered (makeEdge symbol constraint values) afterChildren childrenFacts.1 childrenCovered
          obtain ⟨edges, final, tailDone⟩ :=
            buildEdges_completes rest staged.2 environment edgeResult.2 edgeFacts.1 edgeCovered
          refine ⟨edgeResult.1 :: edges, final, ?_⟩
          simp only [buildEdges, childrenDone, Outcome.bind, work]
          change (buildEdges rest environment edgeResult.2).bind _ = _
          rw [tailDone]
          rfl
termination_by sizeOf expressions
end

/-- The closed source executor completes directly from its finite dependency condition. -/
theorem closed_completes [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (staged : Staged expression) : ∃ value final, build expression [] empty = .done value final :=
  build_completes expression staged [] empty empty_valid empty_correct.2

/-- The first closed run cannot reach an unfinished canonical record. -/
theorem closed_not_pending [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (staged : Staged expression) (key : InternedBinderProtocol.NodeKey) (state : State Symbol Guard) :
    build expression [] empty ≠ .pending key state := by
  obtain ⟨value, final, completed⟩ := closed_completes expression staged
  rw [completed]
  intro impossible
  cases impossible

end MicroCFTA.InternedIndependentCompletion
