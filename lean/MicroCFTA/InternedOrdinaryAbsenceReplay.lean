import MicroCFTA.InternedObservedAbsence
import MicroCFTA.InternedBinderFreeObservations

/-!
# Source-derived exact replay after forbidden-boundary erasure

Two actual ordinary source executions preserve emptiness. If the first
result contains no forbidden reference or Mu identity, their complete
records agree in every coherent common extension of their cache histories.
-/
namespace MicroCFTA.InternedOrdinaryAbsenceReplay
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance
open InternedLiveEdges InternedNonemptyRecords InternedStoredShallowCompletion
open InternedOccurrenceObservations InternedShallowValues InternedObservedAbsence
open InternedBinderProtocol (NodeRef)

/-- Related source inputs give related optional lookups, including the actual empty default. -/
theorem getElem?_related (forbidden : NodeRef → Prop) (first second : List (Value Symbol Guard))
    (paired : Paired (Related forbidden) first second) (index : Nat) :
    Related forbidden (first[index]?.getD .empty) (second[index]?.getD .empty) := by
  induction paired generalizing index with
  | nil => exact related_refl forbidden .empty
  | cons related paired ih => cases index with
    | zero => exact related
    | succ index => exact ih index

/-- Actual complete edge readback retains the requested symbol, child references, and guard. -/
theorem makeEdge_key [DecidableEq (EdgeKey Symbol Guard)] (symbol : Symbol) (constraint : Guard)
    (values : List (Value Symbol Guard)) (state : State Symbol Guard) (coherent : Coherent state) :
    (run (makeEdge symbol constraint values) state).1.entry.key = ⟨symbol, values.map Value.referenceOf, constraint⟩ := by
  have correct := edgeStep_correct ⟨symbol, values.map Value.referenceOf, constraint⟩ (fun entry => .mk entry values) state coherent.valid
  have after := edgeStep_coherent ⟨symbol, values.map Value.referenceOf, constraint⟩ (fun entry => .mk entry values) state coherent
    (fun _ key => ⟨rfl, key, rfl⟩)
  exact (after.edges _ _ correct.2.2).2.1

mutual
/-- Ordinary source syntax derives exact output agreement whenever its forbidden input boundaries disappear. -/
theorem build_related [DecidableEq (EdgeKey Symbol Guard)] (forbidden : NodeRef → Prop) (expression : Syntax Symbol Guard)
    (first second : List (Value Symbol Guard)) (left right : State Symbol Guard)
    (lf : Facts left) (rf : Facts right) (ll : Live left) (rl : Live right)
    (ln : NonemptyRecords left) (rn : NonemptyRecords right)
    (li : Values left first) (ri : Values right second) (paired : Paired (Related forbidden) first second)
    (free : BinderFree expression) :
    ∃ a afterA b afterB, build expression first left = .done a afterA ∧
      build expression second right = .done b afterB ∧
      ∀ common, Facts common → Grows afterA common → Grows afterB common → Related forbidden a b := by
  cases expression with
  | empty => exact ⟨_, _, _, _, by rw [build], by rw [build], fun _ _ _ _ => related_refl forbidden .empty⟩
  | var index => exact ⟨_, _, _, _, by rw [build], by rw [build], fun _ _ _ _ => getElem?_related forbidden first second paired index⟩
  | binder => simp [BinderFree] at free
  | node edges =>
      simp only [BinderFree] at free
      obtain ⟨a, afterA, b, afterB, ea, eb, related⟩ :=
        buildEdges_related forbidden edges first second left right lf rf ll rl ln rn li ri paired free
      have ca := buildEdges_verified edges first left lf li
      have cb := buildEdges_verified edges second right rf ri
      have fa : Facts afterA := by simpa only [ea, Outcome.state] using ca.facts
      have fb : Facts afterB := by simpa only [eb, Outcome.state] using cb.facts
      refine ⟨(run (makeNode a) afterA).1, (run (makeNode a) afterA).2, (run (makeNode b) afterB).1, (run (makeNode b) afterB).2, by simp only [build, ea, Outcome.bind, work],
        by simp only [build, eb, Outcome.bind, work], ?_⟩
      intro common good ga gb
      exact makeNode_related forbidden a b afterA afterB common fa fb good (ca.result a afterA ea) (cb.result b afterB eb)
        (related common good (grows_trans (InternedConstructorTemplates.run_correct (makeNode a) afterA fa.coherent.valid).2 ga)
          (grows_trans (InternedConstructorTemplates.run_correct (makeNode b) afterB fb.coherent.valid).2 gb)) ga gb
  | union members =>
      simp only [BinderFree] at free
      obtain ⟨a, afterA, b, afterB, ea, eb, related⟩ :=
        buildMany_related forbidden members first second left right lf rf ll rl ln rn li ri paired free
      have ca := buildMany_verified members first left lf li
      have cb := buildMany_verified members second right rf ri
      have fa : Facts afterA := by simpa only [ea, Outcome.state] using ca.facts
      have fb : Facts afterB := by simpa only [eb, Outcome.state] using cb.facts
      have la : Live afterA := by simpa only [ea, Outcome.state] using buildMany_live members first left ll
      have lb : Live afterB := by simpa only [eb, Outcome.state] using buildMany_live members second right rl
      have na : NonemptyRecords afterA := by simpa only [ea, Outcome.state] using buildMany_nonempty members first left ln
      have nb : NonemptyRecords afterB := by simpa only [eb, Outcome.state] using buildMany_nonempty members second right rn
      refine ⟨(run (makeUnion a) afterA).1, (run (makeUnion a) afterA).2, (run (makeUnion b) afterB).1, (run (makeUnion b) afterB).2, by simp only [build, ea, Outcome.bind, work],
        by simp only [build, eb, Outcome.bind, work], ?_⟩
      intro common good ga gb
      exact makeUnion_related forbidden a b afterA afterB common fa fb la lb na nb (ca.result a afterA ea) (cb.result b afterB eb)
        (related common good (grows_trans (InternedConstructorTemplates.run_correct (makeUnion a) afterA fa.coherent.valid).2 ga)
          (grows_trans (InternedConstructorTemplates.run_correct (makeUnion b) afterB fb.coherent.valid).2 gb)) ga gb
termination_by sizeOf expression

/-- Ordered child computations derive paired exact absence observations in their common cache history. -/
theorem buildMany_related [DecidableEq (EdgeKey Symbol Guard)] (forbidden : NodeRef → Prop) (expressions : List (Syntax Symbol Guard))
    (first second : List (Value Symbol Guard)) (left right : State Symbol Guard)
    (lf : Facts left) (rf : Facts right) (ll : Live left) (rl : Live right)
    (ln : NonemptyRecords left) (rn : NonemptyRecords right)
    (li : Values left first) (ri : Values right second) (paired : Paired (Related forbidden) first second)
    (free : ManyBinderFree expressions) :
    ∃ a afterA b afterB, buildMany expressions first left = .done a afterA ∧
      buildMany expressions second right = .done b afterB ∧
      ∀ common, Facts common → Grows afterA common → Grows afterB common → Paired (Related forbidden) a b := by
  cases expressions with
  | nil => exact ⟨[], left, [], right, by rw [buildMany], by rw [buildMany], fun _ _ _ _ => .nil⟩
  | cons expression rest =>
      simp only [ManyBinderFree] at free
      obtain ⟨a, afterA, b, afterB, ea, eb, related⟩ :=
        build_related forbidden expression first second left right lf rf ll rl ln rn li ri paired free.1
      have ca := build_verified expression first left lf li
      have cb := build_verified expression second right rf ri
      have fa : Facts afterA := by simpa only [ea, Outcome.state] using ca.facts
      have fb : Facts afterB := by simpa only [eb, Outcome.state] using cb.facts
      have la : Live afterA := by simpa only [ea, Outcome.state] using build_live expression first left ll
      have lb : Live afterB := by simpa only [eb, Outcome.state] using build_live expression second right rl
      have na : NonemptyRecords afterA := by simpa only [ea, Outcome.state] using build_nonempty expression first left ln
      have nb : NonemptyRecords afterB := by simpa only [eb, Outcome.state] using build_nonempty expression second right rn
      have ia : Values afterA first := fun value member => by simpa only [ea, Outcome.state] using ca.available value (li value member)
      have ib : Values afterB second := fun value member => by simpa only [eb, Outcome.state] using cb.available value (ri value member)
      obtain ⟨as, finalA, bs, finalB, es, et, tail⟩ :=
        buildMany_related forbidden rest first second afterA afterB fa fb la lb na nb ia ib paired free.2
      have growsA : Grows afterA finalA := by simpa only [es, Outcome.state] using (buildMany_correct rest first afterA fa.coherent.valid).2
      have growsB : Grows afterB finalB := by simpa only [et, Outcome.state] using (buildMany_correct rest second afterB fb.coherent.valid).2
      exact ⟨a :: as, finalA, b :: bs, finalB, by simp only [buildMany, ea, es, Outcome.bind],
        by simp only [buildMany, eb, et, Outcome.bind], fun common good ga gb =>
          .cons (related common good (grows_trans growsA ga) (grows_trans growsB gb)) (tail common good ga gb)⟩
termination_by sizeOf expressions

/-- Source edge symbols, guards, and actual complete child payloads preserve the observation before normalization. -/
theorem buildEdges_related [DecidableEq (EdgeKey Symbol Guard)] (forbidden : NodeRef → Prop) (expressions : List (EdgeSyntax Symbol Guard))
    (first second : List (Value Symbol Guard)) (left right : State Symbol Guard)
    (lf : Facts left) (rf : Facts right) (ll : Live left) (rl : Live right)
    (ln : NonemptyRecords left) (rn : NonemptyRecords right)
    (li : Values left first) (ri : Values right second) (paired : Paired (Related forbidden) first second)
    (free : EdgesBinderFree expressions) :
    ∃ a afterA b afterB, buildEdges expressions first left = .done a afterA ∧
      buildEdges expressions second right = .done b afterB ∧
      ∀ common, Facts common → Grows afterA common → Grows afterB common → Paired (EdgeRelated forbidden) a b := by
  cases expressions with
  | nil => exact ⟨[], left, [], right, by rw [buildEdges], by rw [buildEdges], fun _ _ _ _ => .nil⟩
  | cons expression rest =>
      cases expression with
      | mk symbol constraint children =>
          simp only [EdgesBinderFree] at free
          obtain ⟨a, afterA, b, afterB, ea, eb, related⟩ :=
            buildMany_related forbidden children first second left right lf rf ll rl ln rn li ri paired free.1
          have ca := buildMany_verified children first left lf li
          have cb := buildMany_verified children second right rf ri
          have fa : Facts afterA := by simpa only [ea, Outcome.state] using ca.facts
          have fb : Facts afterB := by simpa only [eb, Outcome.state] using cb.facts
          have la : Live afterA := by simpa only [ea, Outcome.state] using buildMany_live children first left ll
          have lb : Live afterB := by simpa only [eb, Outcome.state] using buildMany_live children second right rl
          have na : NonemptyRecords afterA := by simpa only [ea, Outcome.state] using buildMany_nonempty children first left ln
          have nb : NonemptyRecords afterB := by simpa only [eb, Outcome.state] using buildMany_nonempty children second right rn
          let edgeA := run (makeEdge symbol constraint a) afterA
          let edgeB := run (makeEdge symbol constraint b) afterB
          have va := ca.result a afterA ea
          have vb := cb.result b afterB eb
          have xa := edge_verified symbol constraint a afterA fa va
          have xb := edge_verified symbol constraint b afterB fb vb
          have ia : Values edgeA.2 first := fun value member => xa.available value (by simpa only [ea, Outcome.state] using ca.available value (li value member))
          have ib : Values edgeB.2 second := fun value member => xb.available value (by simpa only [eb, Outcome.state] using cb.available value (ri value member))
          obtain ⟨as, finalA, bs, finalB, es, et, tail⟩ :=
            buildEdges_related forbidden rest first second edgeA.2 edgeB.2 xa.facts xb.facts la lb na nb ia ib paired free.2
          have growsA : Grows edgeA.2 finalA := by simpa only [es, Outcome.state] using (buildEdges_correct rest first edgeA.2 xa.facts.coherent.valid).2
          have growsB : Grows edgeB.2 finalB := by simpa only [et, Outcome.state] using (buildEdges_correct rest second edgeB.2 xb.facts.coherent.valid).2
          refine ⟨edgeA.1 :: as, finalA, edgeB.1 :: bs, finalB,
            by simp only [buildEdges, ea, Outcome.bind, work]; change (buildEdges rest first edgeA.2).bind _ = _; simp only [es, Outcome.bind]; rfl,
            by simp only [buildEdges, eb, Outcome.bind, work]; change (buildEdges rest second edgeB.2).bind _ = _; simp only [et, Outcome.bind]; rfl, ?_⟩
          intro common good ga gb
          refine .cons ⟨?_, ?_, ?_⟩ (tail common good ga gb)
          · simp only [edgeA, edgeB, makeEdge_key _ _ _ _ fa.coherent, makeEdge_key _ _ _ _ fb.coherent]
          · simp only [edgeA, edgeB, makeEdge_key _ _ _ _ fa.coherent, makeEdge_key _ _ _ _ fb.coherent]
          · rw [makeEdge_children symbol constraint a afterA fa.coherent fa.cached va,
              makeEdge_children symbol constraint b afterB fb.coherent fb.cached vb]
            exact related common good (grows_trans xa.growth (grows_trans growsA ga)) (grows_trans xb.growth (grows_trans growsB gb))
termination_by sizeOf expressions
end

/-- Two actual completed ordinary source traces return the exact same record when the first output has no forbidden boundary. -/
theorem build_equal [DecidableEq (EdgeKey Symbol Guard)] (forbidden : NodeRef → Prop) (expression : Syntax Symbol Guard)
    (first second : List (Value Symbol Guard)) (left right common : State Symbol Guard)
    (lf : Facts left) (rf : Facts right) (cf : Facts common) (ll : Live left) (rl : Live right)
    (ln : NonemptyRecords left) (rn : NonemptyRecords right)
    (li : Values left first) (ri : Values right second) (paired : Paired (Related forbidden) first second)
    (free : BinderFree expression) (a b : Value Symbol Guard) (afterA afterB : State Symbol Guard)
    (leftDone : build expression first left = .done a afterA) (rightDone : build expression second right = .done b afterB)
    (lg : Grows afterA common) (rg : Grows afterB common) (clear : Clear forbidden a) : a = b := by
  obtain ⟨original, firstFinal, other, secondFinal, ea, eb, related⟩ :=
    build_related forbidden expression first second left right lf rf ll rl ln rn li ri paired free
  have aSame := ea.symm.trans leftDone
  have bSame := eb.symm.trans rightDone
  simp only [Outcome.done.injEq] at aSame bSame
  obtain ⟨rfl, rfl⟩ := aSame
  obtain ⟨rfl, rfl⟩ := bSame
  exact (related common cf lg rg).2 clear

end MicroCFTA.InternedOrdinaryAbsenceReplay
