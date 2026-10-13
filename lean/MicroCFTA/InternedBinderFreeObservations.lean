import MicroCFTA.InternedOccurrenceObservations
import MicroCFTA.InternedShallowValues

/-!
# Source-derived observations for ordinary and union callbacks

The same binder-free syntax runs in two source states. Each execution
completes. Paired inputs determine the emptiness and occurrence costs of
both actual outputs through every source normalization branch.
-/
namespace MicroCFTA.InternedBinderFreeObservations
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance
open InternedLiveEdges InternedNonemptyRecords InternedStoredShallowCompletion
open InternedOccurrenceObservations InternedShallowValues
open InternedBinderProtocol (Reference)

mutual
/-- Actual constructor work derives the output observation from corresponding lexical inputs. -/
theorem build_same [DecidableEq (EdgeKey Symbol Guard)] (name : Reference) (expression : Syntax Symbol Guard)
    (first second : List (Value Symbol Guard)) (left right : State Symbol Guard)
    (lf : Facts left) (rf : Facts right) (ll : Live left) (rl : Live right)
    (ln : NonemptyRecords left) (rn : NonemptyRecords right)
    (li : Values left first) (ri : Values right second) (paired : Paired (Same name) first second)
    (free : BinderFree expression) :
    ∃ a afterA b afterB, build expression first left = .done a afterA ∧
      build expression second right = .done b afterB ∧ Same name a b := by
  cases expression with
  | empty => exact ⟨_, _, _, _, by rw [build], by rw [build], same_refl name .empty⟩
  | var index => exact ⟨_, _, _, _, by rw [build], by rw [build], getElem?_same name first second paired index⟩
  | binder => simp [BinderFree] at free
  | node edges =>
      simp only [BinderFree] at free
      obtain ⟨a, afterA, b, afterB, ea, eb, related⟩ :=
        buildEdges_same name edges first second left right lf rf ll rl ln rn li ri paired free
      have ca := buildEdges_verified edges first left lf li
      have cb := buildEdges_verified edges second right rf ri
      have fa : Facts afterA := by simpa only [ea, Outcome.state] using ca.facts
      have fb : Facts afterB := by simpa only [eb, Outcome.state] using cb.facts
      exact ⟨_, (run (makeNode a) afterA).2, _, (run (makeNode b) afterB).2, by simp only [build, ea, Outcome.bind, work],
        by simp only [build, eb, Outcome.bind, work],
        makeNode_same name a b afterA afterB fa.coherent fb.coherent fa.linked fb.linked
          (ca.result a afterA ea) (cb.result b afterB eb) related⟩
  | union members =>
      simp only [BinderFree] at free
      obtain ⟨a, afterA, b, afterB, ea, eb, related⟩ :=
        buildMany_same name members first second left right lf rf ll rl ln rn li ri paired free
      have ca := buildMany_verified members first left lf li
      have cb := buildMany_verified members second right rf ri
      have fa : Facts afterA := by simpa only [ea, Outcome.state] using ca.facts
      have fb : Facts afterB := by simpa only [eb, Outcome.state] using cb.facts
      have la : Live afterA := by simpa only [ea, Outcome.state] using buildMany_live members first left ll
      have lb : Live afterB := by simpa only [eb, Outcome.state] using buildMany_live members second right rl
      have na : NonemptyRecords afterA := by simpa only [ea, Outcome.state] using buildMany_nonempty members first left ln
      have nb : NonemptyRecords afterB := by simpa only [eb, Outcome.state] using buildMany_nonempty members second right rn
      exact ⟨_, (run (makeUnion a) afterA).2, _, (run (makeUnion b) afterB).2, by simp only [build, ea, Outcome.bind, work],
        by simp only [build, eb, Outcome.bind, work],
        makeUnion_same name a b afterA afterB fa.coherent fb.coherent fa.cached fb.cached fa.linked fb.linked
          la lb na nb (ca.result a afterA ea) (cb.result b afterB eb) related⟩
termination_by sizeOf expression

/-- Both ordered child schedules preserve the observation through all earlier cache effects. -/
theorem buildMany_same [DecidableEq (EdgeKey Symbol Guard)] (name : Reference) (expressions : List (Syntax Symbol Guard))
    (first second : List (Value Symbol Guard)) (left right : State Symbol Guard)
    (lf : Facts left) (rf : Facts right) (ll : Live left) (rl : Live right)
    (ln : NonemptyRecords left) (rn : NonemptyRecords right)
    (li : Values left first) (ri : Values right second) (paired : Paired (Same name) first second)
    (free : ManyBinderFree expressions) :
    ∃ a afterA b afterB, buildMany expressions first left = .done a afterA ∧
      buildMany expressions second right = .done b afterB ∧ Paired (Same name) a b := by
  cases expressions with
  | nil => exact ⟨[], left, [], right, by rw [buildMany], by rw [buildMany], .nil⟩
  | cons expression rest =>
      simp only [ManyBinderFree] at free
      obtain ⟨a, afterA, b, afterB, ea, eb, related⟩ :=
        build_same name expression first second left right lf rf ll rl ln rn li ri paired free.1
      have ca := build_verified expression first left lf li
      have cb := build_verified expression second right rf ri
      have fa : Facts afterA := by simpa only [ea, Outcome.state] using ca.facts
      have fb : Facts afterB := by simpa only [eb, Outcome.state] using cb.facts
      have la : Live afterA := by simpa only [ea, Outcome.state] using build_live expression first left ll
      have lb : Live afterB := by simpa only [eb, Outcome.state] using build_live expression second right rl
      have na : NonemptyRecords afterA := by simpa only [ea, Outcome.state] using build_nonempty expression first left ln
      have nb : NonemptyRecords afterB := by simpa only [eb, Outcome.state] using build_nonempty expression second right rn
      have ia : Values afterA first := fun value member => by
        simpa only [ea, Outcome.state] using ca.available value (li value member)
      have ib : Values afterB second := fun value member => by
        simpa only [eb, Outcome.state] using cb.available value (ri value member)
      obtain ⟨as, finalA, bs, finalB, es, et, tail⟩ :=
        buildMany_same name rest first second afterA afterB fa fb la lb na nb ia ib paired free.2
      exact ⟨a :: as, finalA, b :: bs, finalB, by simp only [buildMany, ea, es, Outcome.bind],
        by simp only [buildMany, eb, et, Outcome.bind], .cons related tail⟩
termination_by sizeOf expressions

/-- Edge interning retains each actual paired child list in the complete cached payload. -/
theorem buildEdges_same [DecidableEq (EdgeKey Symbol Guard)] (name : Reference) (expressions : List (EdgeSyntax Symbol Guard))
    (first second : List (Value Symbol Guard)) (left right : State Symbol Guard)
    (lf : Facts left) (rf : Facts right) (ll : Live left) (rl : Live right)
    (ln : NonemptyRecords left) (rn : NonemptyRecords right)
    (li : Values left first) (ri : Values right second) (paired : Paired (Same name) first second)
    (free : EdgesBinderFree expressions) :
    ∃ a afterA b afterB, buildEdges expressions first left = .done a afterA ∧
      buildEdges expressions second right = .done b afterB ∧
      Paired (fun x y => Paired (Same name) x.children y.children) a b := by
  cases expressions with
  | nil => exact ⟨[], left, [], right, by rw [buildEdges], by rw [buildEdges], .nil⟩
  | cons expression rest =>
      cases expression with
      | mk symbol constraint children =>
          simp only [EdgesBinderFree] at free
          obtain ⟨a, afterA, b, afterB, ea, eb, related⟩ :=
            buildMany_same name children first second left right lf rf ll rl ln rn li ri paired free.1
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
          have observed : Paired (Same name) edgeA.1.children edgeB.1.children := by
            rw [makeEdge_children symbol constraint a afterA fa.coherent fa.cached va,
              makeEdge_children symbol constraint b afterB fb.coherent fb.cached vb]
            exact related
          have ia : Values edgeA.2 first := fun value member => xa.available value (by
            simpa only [ea, Outcome.state] using ca.available value (li value member))
          have ib : Values edgeB.2 second := fun value member => xb.available value (by
            simpa only [eb, Outcome.state] using cb.available value (ri value member))
          obtain ⟨as, finalA, bs, finalB, es, et, tail⟩ :=
            buildEdges_same name rest first second edgeA.2 edgeB.2 xa.facts xb.facts la lb na nb ia ib paired free.2
          exact ⟨edgeA.1 :: as, finalA, edgeB.1 :: bs, finalB,
            by simp only [buildEdges, ea, Outcome.bind, work]; change (buildEdges rest first edgeA.2).bind _ = _; simp only [es, Outcome.bind]; rfl,
            by simp only [buildEdges, eb, Outcome.bind, work]; change (buildEdges rest second edgeB.2).bind _ = _; simp only [et, Outcome.bind]; rfl, .cons observed tail⟩
termination_by sizeOf expressions
end

end MicroCFTA.InternedBinderFreeObservations
