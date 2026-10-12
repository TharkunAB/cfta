import MicroCFTA.InternedErasureCorrespondence
import MicroCFTA.InternedRecursiveErasure

/-!
# First-run completion when changed dependencies erase below constructors

Nested binder bodies can erase their immediate outer input below nodes,
unions, and further binders. Syntax induction derives the first execution.
Normalized source-call correspondence then derives each later ordinary
residual, without a successful first-run or stable key premise.
-/
namespace MicroCFTA.InternedDeepErasureCompletion
open InternedConstructorTemplates InternedNestedConstruction InternedRecordCoherence
open InternedNestedSpecialization InternedNestedCoverage InternedNestedCoherence
open InternedNestedFacts InternedNestedProvenance InternedProbeProvenance
open InternedErasureResidual InternedErasureSyntax InternedErasureCorrespondence
open InternedRecursiveErasure (binder_from_residual)
open InternedErasedEdgeReplay (run_coherent)

mutual
/-- Every nested binder has a recursively admitted body whose immediate outer dependency erases by source constructors. -/
def Admitted : Syntax Symbol Guard → Prop
  | .empty | .var _ => True
  | .node edges => EdgesAdmitted edges
  | .union members => ManyAdmitted members
  | .binder _ expression => Erased 1 expression ∧ Admitted expression
termination_by expression => sizeOf expression

/-- Each child admits the same syntax-derived residual construction. -/
def ManyAdmitted : List (Syntax Symbol Guard) → Prop
  | [] => True
  | first :: rest => Admitted first ∧ ManyAdmitted rest
termination_by expressions => sizeOf expressions

/-- Edge declarations preserve each child's exact erased-dependency shape. -/
def EdgesAdmitted : List (EdgeSyntax Symbol Guard) → Prop
  | [] => True
  | .mk _ _ children :: rest => ManyAdmitted children ∧ EdgesAdmitted rest
termination_by expressions => sizeOf expressions
end

mutual
/-- A first source execution derives its complete records and finite ordinary work for every changed local input. -/
theorem build_residual [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (admitted : Admitted expression) (initial : Value Symbol Guard) (captures : List (Value Symbol Guard))
    (before : State Symbol Guard) (coherent : Coherent before) (covered : Covered [] before) :
    ∃ value final, ∃ code : Value Symbol Guard → Work Symbol Guard (Value Symbol Guard),
      build expression (initial :: captures) before = .done value final ∧
      Coherent final ∧ Covered [] final ∧ Grows before final ∧
      (∀ argument, Safe (code argument) ∧ Ordinary (code argument)) ∧
      ∀ argument after, Coherent after → Grows final after →
        build expression (argument :: captures) after = work (code argument) after := by
  cases expression with
  | empty =>
      exact ⟨.empty, before, fun _ => .pure .empty, by simp only [build], coherent, covered, grows_refl _,
        fun _ => ⟨trivial, trivial⟩, fun _ _ _ _ => by simp only [build, work, run]⟩
  | var index =>
      refine ⟨(initial :: captures)[index]?.getD .empty, before,
        fun argument => .pure ((argument :: captures)[index]?.getD .empty),
        by simp only [build], coherent, covered, grows_refl _, fun _ => ⟨trivial, trivial⟩, ?_⟩
      intro argument after _ _
      simp only [build, work, run]
  | node edges =>
      simp only [Admitted] at admitted
      obtain ⟨values, middle, code, completed, middleCoherent, middleCovered, growth, safe, residual⟩ :=
        buildEdges_residual edges admitted initial captures before coherent covered
      let result := run (makeNode values) middle
      have later := InternedConstructorTemplates.run_correct (makeNode values) middle middleCoherent.valid
      refine ⟨result.1, result.2, fun argument => (code argument).bind makeNode, ?_,
        run_coherent _ _ (makeNode_safe _) middleCoherent,
        run_covered _ _ middleCoherent.valid middleCovered, grows_trans growth later.2,
        fun argument => ⟨safe_bind _ _ (safe argument).1 makeNode_safe,
          ordinary_bind _ _ (safe argument).2 makeNode_ordinary⟩, ?_⟩
      · simp only [build, completed, Outcome.bind, work, result]
      · intro argument after afterCoherent afterGrowth
        simp only [build, residual argument after afterCoherent (grows_trans later.2 afterGrowth), work_bind]
  | union members =>
      simp only [Admitted] at admitted
      obtain ⟨values, middle, code, completed, middleCoherent, middleCovered, growth, safe, residual⟩ :=
        buildMany_residual members admitted initial captures before coherent covered
      let result := run (makeUnion values) middle
      have later := InternedConstructorTemplates.run_correct (makeUnion values) middle middleCoherent.valid
      refine ⟨result.1, result.2, fun argument => (code argument).bind makeUnion, ?_,
        run_coherent _ _ (makeUnion_safe _) middleCoherent,
        run_covered _ _ middleCoherent.valid middleCovered, grows_trans growth later.2,
        fun argument => ⟨safe_bind _ _ (safe argument).1 makeUnion_safe,
          ordinary_bind _ _ (safe argument).2 makeUnion_ordinary⟩, ?_⟩
      · simp only [build, completed, Outcome.bind, work, result]
      · intro argument after afterCoherent afterGrowth
        simp only [build, residual argument after afterCoherent (grows_trans later.2 afterGrowth), work_bind]
  | binder smart expression =>
      simp only [Admitted] at admitted
      obtain ⟨first, afterFirst, firstCode, firstDone, firstCoherent, firstCovered, _, firstSafe, firstResidual⟩ :=
        build_residual expression admitted.2 (.reference .depth) (initial :: captures) before coherent covered
      obtain ⟨value, final, completed⟩ := binder_from_residual smart expression (initial :: captures) before
        first afterFirst firstCode firstDone firstCoherent firstCovered firstSafe firstResidual
      have finalCoherent : Coherent final := by
        simpa only [completed, Outcome.state] using build_coherent (.binder smart expression) (initial :: captures) before coherent
      have finalCovered : Covered [] final :=
        build_covered (.binder smart expression) (initial :: captures) before coherent.valid covered value final completed
      have finalGrowth : Grows before final := by
        simpa only [completed, Outcome.state] using (build_correct (.binder smart expression) (initial :: captures) before coherent.valid).2
      have sourceErased : Erased 0 (.binder smart expression) := .binder 0 smart expression admitted.1
      have replay : ∀ argument, Residual value final (build (.binder smart expression) (argument :: captures)) := by
        intro argument
        apply build_erased sourceErased (initial :: captures) (argument :: captures) _ before value final coherent completed
        intro index different
        cases index with
        | zero => exact False.elim (different rfl)
        | succ index => rfl
      let code : Value Symbol Guard → Work Symbol Guard (Value Symbol Guard) := fun argument => Classical.choose (replay argument)
      have certified : ∀ argument, Safe (code argument) ∧ Ordinary (code argument) ∧
          ∀ after, Coherent after → Grows final after →
            build (.binder smart expression) (argument :: captures) after = work (code argument) after ∧
              (run (code argument) after).1 = value := fun argument => Classical.choose_spec (replay argument)
      exact ⟨value, final, code, completed, finalCoherent, finalCovered, finalGrowth,
        fun argument => ⟨(certified argument).1, (certified argument).2.1⟩,
        fun argument after afterCoherent growth => ((certified argument).2.2 after afterCoherent growth).1⟩
termination_by sizeOf expression

/-- Residual child work preserves source order and the exact later effects of every erased-dependent call. -/
theorem buildMany_residual [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (admitted : ManyAdmitted expressions) (initial : Value Symbol Guard) (captures : List (Value Symbol Guard))
    (before : State Symbol Guard) (coherent : Coherent before) (covered : Covered [] before) :
    ∃ values final, ∃ code : Value Symbol Guard → Work Symbol Guard (List (Value Symbol Guard)),
      buildMany expressions (initial :: captures) before = .done values final ∧
      Coherent final ∧ Covered [] final ∧ Grows before final ∧
      (∀ argument, Safe (code argument) ∧ Ordinary (code argument)) ∧
      ∀ argument after, Coherent after → Grows final after →
        buildMany expressions (argument :: captures) after = work (code argument) after := by
  cases expressions with
  | nil =>
      exact ⟨[], before, fun _ => .pure [], by simp only [buildMany], coherent, covered, grows_refl _,
        fun _ => ⟨trivial, trivial⟩, fun _ _ _ _ => by simp only [buildMany, work, run]⟩
  | cons first rest =>
      simp only [ManyAdmitted] at admitted
      obtain ⟨value, middle, firstCode, firstDone, middleCoherent, middleCovered, firstGrowth, firstSafe, firstResidual⟩ :=
        build_residual first admitted.1 initial captures before coherent covered
      obtain ⟨values, final, tailCode, tailDone, finalCoherent, finalCovered, tailGrowth, tailSafe, tailResidual⟩ :=
        buildMany_residual rest admitted.2 initial captures middle middleCoherent middleCovered
      refine ⟨value :: values, final, fun argument => (firstCode argument).bind fun value =>
          (tailCode argument).bind fun values => .pure (value :: values), ?_, finalCoherent, finalCovered,
        grows_trans firstGrowth tailGrowth, fun argument => ⟨?_, ?_⟩, ?_⟩
      · simp only [buildMany, firstDone, tailDone, Outcome.bind]
      · exact safe_bind _ _ (firstSafe argument).1 (fun _ => safe_bind _ _ (tailSafe argument).1 (fun _ => trivial))
      · exact ordinary_bind _ _ (firstSafe argument).2 (fun _ => ordinary_bind _ _ (tailSafe argument).2 (fun _ => trivial))
      · intro argument after afterCoherent afterGrowth
        have firstLater := firstResidual argument after afterCoherent (grows_trans tailGrowth afterGrowth)
        have nextCoherent := run_coherent (firstCode argument) after (firstSafe argument).1 afterCoherent
        have nextGrowth := (InternedConstructorTemplates.run_correct (firstCode argument) after afterCoherent.valid).2
        have tailLater := tailResidual argument (run (firstCode argument) after).2 nextCoherent (grows_trans afterGrowth nextGrowth)
        simp only [buildMany, firstLater, work, Outcome.bind, run_bind]
        rw [tailLater]
        simp only [work, run]
termination_by sizeOf expressions

/-- Residual edges retain the source child order and both actual cache families. -/
theorem buildEdges_residual [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (admitted : EdgesAdmitted expressions) (initial : Value Symbol Guard) (captures : List (Value Symbol Guard))
    (before : State Symbol Guard) (coherent : Coherent before) (covered : Covered [] before) :
    ∃ values final, ∃ code : Value Symbol Guard → Work Symbol Guard (List (EdgeValue Symbol Guard)),
      buildEdges expressions (initial :: captures) before = .done values final ∧
      Coherent final ∧ Covered [] final ∧ Grows before final ∧
      (∀ argument, Safe (code argument) ∧ Ordinary (code argument)) ∧
      ∀ argument after, Coherent after → Grows final after →
        buildEdges expressions (argument :: captures) after = work (code argument) after := by
  cases expressions with
  | nil =>
      exact ⟨[], before, fun _ => .pure [], by simp only [buildEdges], coherent, covered, grows_refl _,
        fun _ => ⟨trivial, trivial⟩, fun _ _ _ _ => by simp only [buildEdges, work, run]⟩
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          simp only [EdgesAdmitted] at admitted
          obtain ⟨values, middle, childCode, childrenDone, middleCoherent, middleCovered, childrenGrowth, childrenSafe, childrenResidual⟩ :=
            buildMany_residual children admitted.1 initial captures before coherent covered
          let edgeResult := run (makeEdge symbol constraint values) middle
          have edgeCoherent := run_coherent (makeEdge symbol constraint values) middle (makeEdge_safe _ _ _) middleCoherent
          have edgeCovered := run_covered (makeEdge symbol constraint values) middle middleCoherent.valid middleCovered
          have edgeGrowth := (InternedConstructorTemplates.run_correct (makeEdge symbol constraint values) middle middleCoherent.valid).2
          obtain ⟨edges, final, tailCode, tailDone, finalCoherent, finalCovered, tailGrowth, tailSafe, tailResidual⟩ :=
            buildEdges_residual rest admitted.2 initial captures edgeResult.2 edgeCoherent edgeCovered
          refine ⟨edgeResult.1 :: edges, final, fun argument => (childCode argument).bind fun values =>
              (makeEdge symbol constraint values).bind fun edge => (tailCode argument).bind fun edges => .pure (edge :: edges),
            ?_, finalCoherent, finalCovered, grows_trans childrenGrowth (grows_trans edgeGrowth tailGrowth),
            fun argument => ⟨?_, ?_⟩, ?_⟩
          · simp only [buildEdges, childrenDone, work, Outcome.bind]
            change (buildEdges rest (initial :: captures) edgeResult.2).bind _ = _
            rw [tailDone]
            rfl
          · exact safe_bind _ _ (childrenSafe argument).1 (fun _ => safe_bind _ _ (makeEdge_safe _ _ _)
              (fun _ => safe_bind _ _ (tailSafe argument).1 (fun _ => trivial)))
          · exact ordinary_bind _ _ (childrenSafe argument).2 (fun _ => ordinary_bind _ _ (by simp [makeEdge, Ordinary])
              (fun _ => ordinary_bind _ _ (tailSafe argument).2 (fun _ => trivial)))
          · intro argument after afterCoherent afterGrowth
            have childrenLater := childrenResidual argument after afterCoherent
              (grows_trans edgeGrowth (grows_trans tailGrowth afterGrowth))
            let childrenResult := run (childCode argument) after
            have nextCoherent := run_coherent (childCode argument) after (childrenSafe argument).1 afterCoherent
            have nextGrowth := (InternedConstructorTemplates.run_correct (childCode argument) after afterCoherent.valid).2
            let nextEdge := run (makeEdge symbol constraint childrenResult.1) childrenResult.2
            have nextEdgeCoherent := run_coherent (makeEdge symbol constraint childrenResult.1) childrenResult.2 (makeEdge_safe _ _ _) nextCoherent
            have nextEdgeGrowth := (InternedConstructorTemplates.run_correct (makeEdge symbol constraint childrenResult.1) childrenResult.2 nextCoherent.valid).2
            have tailLater := tailResidual argument nextEdge.2 nextEdgeCoherent
              (grows_trans afterGrowth (grows_trans nextGrowth nextEdgeGrowth))
            simp only [buildEdges, childrenLater, work, Outcome.bind, run_bind]
            rw [tailLater]
            simp only [work, run, nextEdge, childrenResult]
termination_by sizeOf expressions
end

/-- Every admitted first body trace supplies the exact residual used by its enclosing source binder. -/
theorem binder_completes [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (expression : Syntax Symbol Guard)
    (admitted : Admitted expression) (captures : List (Value Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) (covered : Covered [] state) :
    ∃ value final, build (.binder smart expression) captures state = .done value final := by
  obtain ⟨initial, afterInitial, code, initialDone, initialCoherent, initialCovered, _, safe, residual⟩ :=
    build_residual expression admitted (.reference .depth) captures state coherent covered
  exact binder_from_residual smart expression captures state initial afterInitial code initialDone
    initialCoherent initialCovered safe residual

/-- Recursively erased dependencies complete from empty caches without an initial replay assumption. -/
theorem closed_completes [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (expression : Syntax Symbol Guard)
    (admitted : Admitted expression) : ∃ value final, build (.binder smart expression) [] empty = .done value final :=
  binder_completes smart expression admitted [] empty empty_correct.1 empty_correct.2

/-- First completion derives full record provenance, complete coverage, and exact later whole-program replay. -/
theorem closed_complete_record [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (expression : Syntax Symbol Guard)
    (admitted : Admitted expression) :
    ∃ value final, build (.binder smart expression) [] empty = .done value final ∧
      Facts final ∧ Covered [] final ∧ Available final value ∧
      ∀ after, Grows final after → build (.binder smart expression) [] after = .done value after := by
  obtain ⟨value, final, completed⟩ := closed_completes smart expression admitted
  have verified := closed_verified (.binder smart expression)
  refine ⟨value, final, completed, ?_, closed_covered _ value final completed,
    verified.result value final completed, fun after growth => empty_replay _ value final after completed growth⟩
  simpa only [completed, Outcome.state] using verified.facts

end MicroCFTA.InternedDeepErasureCompletion
