import MicroCFTA.InternedNestedErasureReplay
import MicroCFTA.InternedNestedCoverage
import MicroCFTA.InternedNestedProvenance

/-!
# First-run completion with recursively nested erased dependencies

Each inner binder reads its immediate outer variable in an edge with an
empty child. Its other edges can contain further binders of the same
source grammar. Earlier actual traces derive ordinary residual work for
later callbacks. No depth bound or successful initial execution is assumed.
-/
namespace MicroCFTA.InternedRecursiveErasure
open InternedConstructorTemplates InternedNestedConstruction InternedRecordCoherence
open InternedNestedSpecialization InternedNestedCoverage InternedNestedCoherence InternedNestedErasureReplay
open InternedNestedFacts InternedNestedProvenance InternedProbeProvenance
open InternedErasedEdgeReplay (run_coherent)

/-- A derived ordinary residual executes both later callbacks while its enclosing binder is pending. -/
theorem binder_from_residual [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (expression : Syntax Symbol Guard)
    (captures : List (Value Symbol Guard)) (state : State Symbol Guard)
    (initial : Value Symbol Guard) (afterInitial : State Symbol Guard)
    (code : Value Symbol Guard → Work Symbol Guard (Value Symbol Guard))
    (initialDone : build expression (.reference .depth :: captures) state = .done initial afterInitial)
    (initialCoherent : Coherent afterInitial) (initialCovered : Covered [] afterInitial)
    (safe : ∀ argument, Safe (code argument) ∧ Ordinary (code argument))
    (residual : ∀ argument after, Coherent after → Grows afterInitial after →
      build expression (argument :: captures) after = work (code argument) after) :
    ∃ value final, build (.binder smart expression) captures state = .done value final := by
  let callback := fun name current => (build expression (.reference name :: captures) current).bind
    fun value next => work (withoutSelfReference name value) next
  let normalized := fun name => (code (.reference name)).bind (withoutSelfReference name)
  have normalizedSafe : ∀ name, Safe (normalized name) :=
    fun name => safe_bind _ _ (safe (.reference name)).1 (withoutSelfReference_safe name)
  have callbackWork : ∀ name after, Coherent after → Grows afterInitial after →
      callback name after = work (normalized name) after := by
    intro name after afterCoherent growth
    simp only [callback, residual (.reference name) after afterCoherent growth, normalized, work_bind]
  let depthResult := run (withoutSelfReference .depth initial) afterInitial
  have depthDone : callback .depth state = .done depthResult.1 depthResult.2 := by
    simp only [callback, initialDone, Outcome.bind, work, depthResult]
  have depthCoherent := run_coherent (withoutSelfReference .depth initial) afterInitial
    (withoutSelfReference_safe _ _) initialCoherent
  have depthCovered := run_covered (withoutSelfReference .depth initial) afterInitial initialCoherent.valid initialCovered
  have depthGrowth := (InternedConstructorTemplates.run_correct (withoutSelfReference .depth initial)
    afterInitial initialCoherent.valid).2
  let ordinaryResult := run (normalized (.uninterned depthResult.1.depth)) depthResult.2
  have ordinaryDone : callback (.uninterned depthResult.1.depth) depthResult.2 =
      .done ordinaryResult.1 ordinaryResult.2 := callbackWork _ _ depthCoherent depthGrowth
  have ordinaryCoherent := run_coherent (normalized (.uninterned depthResult.1.depth)) depthResult.2
    (normalizedSafe _) depthCoherent
  have ordinaryCovered := run_covered (normalized (.uninterned depthResult.1.depth)) depthResult.2 depthCoherent.valid depthCovered
  have ordinaryGrowth := (InternedConstructorTemplates.run_correct (normalized (.uninterned depthResult.1.depth))
    depthResult.2 depthCoherent.valid).2
  have expanded : build (.binder smart expression) captures state =
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
      have allocatedCoherent := (reserve_correct key ordinaryResult.2 ordinaryCoherent ordinaryCovered).1
      have allocatedGrowth : Grows ordinaryResult.2 allocated :=
        ⟨Cache.extends_refl _, InternedBinderProtocol.intern_grows _ _, Cache.extends_refl _, Cache.extends_refl _⟩
      have actualDone := callbackWork (.interned entry.1.identity) allocated allocatedCoherent
        (grows_trans depthGrowth (grows_trans ordinaryGrowth allocatedGrowth))
      simp only [request, present]
      change ∃ value final, (callback (.interned entry.1.identity) allocated).bind _ = .done value final
      rw [actualDone]
      simp only [work, Outcome.bind]
      exact ⟨_, _, rfl⟩

mutual
/-- Each nested body retains arbitrary admitted live children and declares its changed outer dependency only in the dead edge. -/
def Admitted : Syntax Symbol Guard → Prop
  | .empty | .var _ => True
  | .node edges => EdgesAdmitted edges
  | .union members => ManyAdmitted members
  | .binder _ expression => match expression with
    | .node edges =>
        (∃ live symbol constraint, edges = live ++ [.mk symbol constraint [.var 1, .empty]] ∧
          1 ∉ InternedNestedDependencies.edgeInputs live) ∧ EdgesAdmitted edges
    | _ => False
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
      cases expression with
      | empty | var | union | binder => simp [Admitted] at admitted
      | node edges =>
          simp only [Admitted] at admitted
          obtain ⟨⟨live, symbol, constraint, shape, unused⟩, nested⟩ := admitted
          obtain ⟨first, afterFirst, firstCode, firstDone, firstCoherent, firstCovered, _, firstSafe, firstResidual⟩ :=
            build_residual (.node edges) (by simpa only [Admitted] using nested)
              (.reference .depth) (initial :: captures) before coherent covered
          obtain ⟨value, final, completed⟩ := binder_from_residual smart (.node edges) (initial :: captures) before
            first afterFirst firstCode firstDone firstCoherent firstCovered firstSafe firstResidual
          have finalCoherent : Coherent final := by
            simpa only [completed, Outcome.state] using build_coherent (.binder smart (.node edges)) (initial :: captures) before coherent
          have finalCovered : Covered [] final :=
            build_covered (.binder smart (.node edges)) (initial :: captures) before coherent.valid covered value final completed
          have finalGrowth : Grows before final := by
            simpa only [completed, Outcome.state] using (build_correct (.binder smart (.node edges)) (initial :: captures) before coherent.valid).2
          refine ⟨value, final, fun argument => replayWork symbol constraint argument value, completed,
            finalCoherent, finalCovered, finalGrowth, fun argument => replayWork_safe symbol constraint argument value, ?_⟩
          intro argument after afterCoherent afterGrowth
          rw [shape] at completed ⊢
          exact binder_residual live unused symbol constraint smart initial argument captures before after value final
            coherent afterCoherent completed afterGrowth
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

end MicroCFTA.InternedRecursiveErasure
