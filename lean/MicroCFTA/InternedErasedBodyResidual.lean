import MicroCFTA.InternedNestedErasedEdge

/-!
# Residual ordinary work for erased-dependent nested source bodies

The source can place erased-dependent binder calls in any ordinary child
position. Their first executions complete before the enclosing binder is
reserved. Later executions perform the actual probe effects and read their
earlier complete records. The resulting work contains no Mu request.
-/
namespace MicroCFTA.InternedErasedBodyResidual
open InternedConstructorTemplates InternedNestedConstruction InternedNestedOrdinary
open InternedNestedErasedEdge InternedNestedSpecialization InternedRecordCoherence InternedNestedCoverage
open InternedStagedBinders (Skeleton EdgeSkeleton instantiateEdges)
open InternedErasedEdgeReplay (extension run_coherent)

mutual
/-- Nested calls use the declared empty-child erasure shape; ordinary source syntax is unrestricted. -/
def Admitted : Syntax Symbol Guard → Prop
  | .empty | .var _ => True
  | .node edges => EdgesAdmitted edges
  | .union members => ManyAdmitted members
  | .binder _ expression => ∃ live symbol constraint, expression = source (body live symbol constraint)
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

/-- Execute both ordinary source probes and then return the earlier completed record. -/
def probeWork (template : Template Symbol Guard) (value : Value Symbol Guard) : Work Symbol Guard (Value Symbol Guard) :=
  (compileBody template .depth).bind fun depth =>
    (compileBody template (.uninterned depth.depth)).bind fun _ => .pure value

/-- Repeated probes preserve all real allocation effects before canonical readback. -/
theorem probeWork_run [DecidableEq (EdgeKey Symbol Guard)] (template : Template Symbol Guard)
    (value : Value Symbol Guard) (state : State Symbol Guard) :
    run (probeWork template value) state = (value, (probes template state).2) := by
  simp only [probeWork, run_bind, run, probes]

/-- Every residual probe action uses certified ordinary constructor fields. -/
theorem probeWork_safe (template : Template Symbol Guard) (value : Value Symbol Guard) : Safe (probeWork template value) :=
  safe_bind _ _ (safe_bind _ _ (compile_safe _ _) (withoutSelfReference_safe _))
    (fun _ => safe_bind _ _ (safe_bind _ _ (compile_safe _ _) (withoutSelfReference_safe _)) (fun _ => trivial))

/-- The residual probes cannot request any unfinished Mu payload. -/
theorem probeWork_ordinary (template : Template Symbol Guard) (value : Value Symbol Guard) : Ordinary (probeWork template value) :=
  ordinary_bind _ _ (compileBody_ordinary _ _) (fun _ => ordinary_bind _ _ (compileBody_ordinary _ _) (fun _ => trivial))

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
      obtain ⟨live, symbol, constraint, rfl⟩ := admitted
      let template := extension (instantiateEdges live captures) symbol constraint initial
      let result := internMu template before
      have correct := InternedRecordCoherence.internMu_correct template before coherent covered
      have growth := (InternedConstructorTemplates.internMu_correct template before coherent.valid).2
      refine ⟨finish smart result.1, result.2,
        fun argument => probeWork (extension (instantiateEdges live captures) symbol constraint argument) (finish smart result.1),
        first_build smart live symbol constraint initial captures before coherent covered,
        correct.1, correct.2, growth,
        fun _ => ⟨probeWork_safe _ _, probeWork_ordinary _ _⟩, ?_⟩
      intro argument after afterCoherent afterGrowth
      rw [changed_outer smart live symbol constraint initial argument captures before after coherent afterCoherent afterGrowth]
      simp only [work, probeWork_run, result, template]
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

end MicroCFTA.InternedErasedBodyResidual
