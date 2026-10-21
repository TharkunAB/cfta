import MicroCFTA.SourceCurrentOuterExecutionAncestry
import MicroCFTA.SourceCurrentOuterUntouchedProgress

namespace MicroCFTA.SourceCurrentOuterOwnerPrefix
open Cache InternedConstructorTemplates
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialWorker
open SourceCurrentOuterCopiedWarmHit (Phase)
open SourceCurrentOuterExecutionAncestry (Reached)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "prefixState" => SourceCurrentAllocatedPartialGraph.prefixState
local notation "descend" => SourceCurrentAllocatedPartialGraph.descend
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width : Nat}


private theorem head_cases {first last : Phase width}
    (actual : Reached g s r e p h m c n budget first last) :
    first = last ∨ ∃ middle,
      SourceCurrentOuterExecutionAncestry.Step g s r e p h m c n budget first middle ∧
      Reached g s r e p h m c n budget middle last := by
  induction actual with
  | refl => exact Or.inl rfl
  | snoc earlier step ih =>
      rcases ih with same | ⟨middle,head,tail⟩
      · cases same
        exact Or.inr ⟨_,step,.refl _⟩
      · exact Or.inr ⟨middle,head,tail.snoc step⟩

private def NodeTail (fuel : Nat) (request : NodeRequest) (before : Caller width)
    (last : Phase width) : Prop :=
  last = .node fuel request before ∨
    ∃ (handle : Nat) (captured : NodeRequest) (running : Caller width),
      beginNode request before = (handle,.evaluate captured,running) ∧
      Reached g s r e p h m c n budget (.body fuel captured running) last

private theorem node_tail
    (actual : Reached g s r e p h m c n budget (.node fuel request before) last) :
    NodeTail (g := g) (s := s) (r := r) (e := e) (p := p) (h := h) (m := m) (c := c) (n := n)
      (budget := budget) fuel request before last := by
  rcases head_cases actual with same | ⟨middle,step,remaining⟩
  · exact Or.inl same.symm
  · cases step with
    | node_evaluate started => exact Or.inr ⟨_,_,_,started,remaining⟩

private def WalkFirst (fuel : Nat) (combined : EqValue) (offset : Nat) (values : List Node)
    (before : Caller width) (last : Phase width) : Prop :=
  ∃ (slot childFuel : Nat) (child : Node) (earlier : List Node) (start : Caller width),
    fuel = childFuel + slot + 1 ∧ values[slot]? = some child ∧
    walk fuel g s r e p h m c n budget combined offset (values.take slot) before = .done earlier start ∧
    NodeTail (g := g) (s := s) (r := r) (e := e) (p := p) (h := h) (m := m) (c := c) (n := n)
      (budget := budget) childFuel ⟨(descend start combined (offset + slot)).1,child⟩
      (descend start combined (offset + slot)).2 last

private theorem walk_first (fuel : Nat) :
    ∀ {combined : EqValue} {offset : Nat} {values : List Node} {before : Caller width}
      {candidateFuel : Nat} {candidate : NodeRequest} {current : Caller width},
      Reached g s r e p h m c n budget (.walk fuel combined offset values before)
        (.node candidateFuel candidate current) →
      WalkFirst (g := g) (s := s) (r := r) (e := e) (p := p) (h := h) (m := m) (c := c) (n := n)
        (budget := budget) fuel combined offset values before (.node candidateFuel candidate current) := by
  induction fuel with
  | zero =>
      intro combined offset values before candidateFuel candidate current actual
      rcases head_cases actual with same | ⟨middle,step,remaining⟩
      · cases same
      · cases step
  | succ fuel ih =>
      intro combined offset values before candidateFuel candidate current actual
      rcases head_cases actual with same | ⟨middle,step,remaining⟩
      · cases same
      · cases step with
        | @walk_head next combined offset value rest before =>
            refine ⟨0,next,value,[],before,by omega,rfl,?_,?_⟩
            · simp only [List.take_zero,walk]
            · simpa only [Nat.add_zero] using node_tail remaining
        | @walk_tail next before combined offset value returned middle rest called =>
            obtain ⟨slot,childFuel,child,earlier,start,count,selected,previous,tail⟩ := ih remaining
            refine ⟨slot+1,childFuel,child,returned::earlier,start,by omega,?_,?_,?_⟩
            · simpa only [List.getElem?_cons_succ] using selected
            · simp only [List.take_succ_cons,walk,called,Outcome.bind,previous]
            · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using tail

private theorem descendants_first
    (actual : Reached g s r e p h m c n budget (.descendants fuel inherited parented afterParent)
      (.node candidateFuel candidate current)) :
    ∃ combined,
      (SourceCurrentAllocatedInheritedPrefix.run parented.entry.key.constraint inherited
        afterParent.checked.operations).1 = .ok (some combined) ∧ combined ≠ .contradiction ∧
      WalkFirst (g := g) (s := s) (r := r) (e := e) (p := p) (h := h) (m := m) (c := c) (n := n)
        (budget := budget) fuel combined 0 parented.children (prefixState afterParent parented inherited)
        (.node candidateFuel candidate current) := by
  rcases head_cases actual with same | ⟨middle,step,remaining⟩
  · cases same
  · cases step with
    | descendants_children combinedAt =>
        rcases head_cases remaining with same | ⟨middle,step,remaining⟩
        · cases same
        · cases step with
          | children_walk live => exact ⟨_,combinedAt,live,walk_first _ remaining⟩

private def RowsFirst (fuel : Nat) (inherited : EqValue) (values : List Edge) (before : Caller width)
    (last : Phase width) : Prop :=
  ∃ (skippedRows : List Edge) (original parented : Edge) (rest : List Edge)
    (rowBefore afterParent start : Caller width) (slot childFuel : Nat)
    (combined : EqValue) (earlier : List Node) (child : Node),
    values = skippedRows ++ original :: rest ∧
    Reached g s r e p h m c n budget (.rows fuel inherited values before)
      (.rows (childFuel + slot + 2) inherited (original :: rest) rowBefore) ∧
    edgeCall (childFuel + slot + 1) g s r e p h m c n budget
      ⟨inherited,original⟩ rowBefore = .done parented afterParent ∧
    (SourceCurrentAllocatedInheritedPrefix.run parented.entry.key.constraint inherited
      afterParent.checked.operations).1 = .ok (some combined) ∧ combined ≠ .contradiction ∧
    walk (childFuel + slot + 1) g s r e p h m c n budget combined 0
      (parented.children.take slot) (prefixState afterParent parented inherited) = .done earlier start ∧
    parented.children[slot]? = some child ∧
    NodeTail (g := g) (s := s) (r := r) (e := e) (p := p) (h := h) (m := m) (c := c) (n := n)
      (budget := budget) childFuel ⟨(descend start combined slot).1,child⟩ (descend start combined slot).2 last

private theorem rows_first (fuel : Nat) :
    ∀ {inherited : EqValue} {values : List Edge} {before : Caller width}
      {candidateFuel : Nat} {candidate : NodeRequest} {current : Caller width},
      Reached g s r e p h m c n budget (.rows fuel inherited values before)
        (.node candidateFuel candidate current) →
      RowsFirst (g := g) (s := s) (r := r) (e := e) (p := p) (h := h) (m := m) (c := c) (n := n)
        (budget := budget) fuel inherited values before (.node candidateFuel candidate current) := by
  induction fuel with
  | zero =>
      intro inherited values before candidateFuel candidate current actual
      rcases head_cases actual with same | ⟨middle,step,remaining⟩
      · cases same
      · cases step
  | succ fuel ih =>
      intro inherited values before candidateFuel candidate current actual
      rcases head_cases actual with same | ⟨middle,step,remaining⟩
      · cases same
      · cases step with
        | @rows_edge next inherited original before parented afterParent rest called =>
            obtain ⟨combined,combinedAt,live,slot,childFuel,child,earlier,start,count,selected,previous,tail⟩ :=
              descendants_first remaining
            refine ⟨[],original,parented,rest,before,afterParent,start,slot,childFuel,combined,earlier,child,
              rfl,?_,?_,combinedAt,live,?_,selected,?_⟩
            · have sameFuel : next + 1 = childFuel + slot + 2 := by omega
              simpa only [sameFuel] using (Reached.refl
                (.rows (next + 1) inherited (original::rest) before))
            · simpa only [count] using called
            · simpa only [count] using previous
            · simpa only [Nat.zero_add] using tail
        | @rows_tail next inherited original before parented afterParent result after rest called completed =>
            obtain ⟨skipped,chosen,returned,restValues,rowBefore,afterChosen,start,slot,childFuel,combined,
              earlier,child,split,cut,parent,combinedAt,live,previous,selected,tail⟩ := ih remaining
            refine ⟨original::skipped,chosen,returned,restValues,rowBefore,afterChosen,start,slot,childFuel,
              combined,earlier,child,?_,?_,parent,combinedAt,live,previous,selected,tail⟩
            · simp only [List.cons_append,split]
            · exact (Reached.snoc (.refl _) (.rows_tail called completed)).trans cut

theorem first_child
    {g s r e p h m c n budget bodyFuel candidateFuel : Nat}
    {inherited : EqValue} {ownerEntry ownerDepth ownerFree} {ownerRows : List Edge}
    {before current : Caller width} {candidate : NodeRequest}
    (actual : Reached g s r e p h m c n budget
      (.body bodyFuel ⟨inherited,.node ownerEntry ownerRows ownerDepth ownerFree⟩ before)
      (.node candidateFuel candidate current)) :
    ∃ (skippedRows : List Edge) (original parented : Edge) (rest : List Edge)
      (rowBefore afterParent start : Caller width) (slot childFuel : Nat)
      (combined : EqValue) (earlier : List Node) (child : Node),
      ownerRows = skippedRows ++ original :: rest ∧
      Reached g s r e p h m c n budget
        (.body bodyFuel ⟨inherited,.node ownerEntry ownerRows ownerDepth ownerFree⟩ before)
        (.rows (childFuel + slot + 2) inherited (original :: rest) rowBefore) ∧
      edgeCall (childFuel + slot + 1) g s r e p h m c n budget
        ⟨inherited,original⟩ rowBefore = .done parented afterParent ∧
      (SourceCurrentAllocatedInheritedPrefix.run parented.entry.key.constraint
        inherited afterParent.checked.operations).1 = .ok (some combined) ∧
      combined ≠ .contradiction ∧
      walk (childFuel + slot + 1) g s r e p h m c n budget combined 0
        (parented.children.take slot) (prefixState afterParent parented inherited) = .done earlier start ∧
      parented.children[slot]? = some child ∧
      (((.node candidateFuel candidate current : Phase width) =
          .node childFuel ⟨(descend start combined slot).1,child⟩ (descend start combined slot).2) ∨
        ∃ (handle : Nat) (captured : NodeRequest) (running : Caller width),
          beginNode ⟨(descend start combined slot).1,child⟩ (descend start combined slot).2 =
            (handle,.evaluate captured,running) ∧
          Reached g s r e p h m c n budget (.body childFuel captured running)
            (.node candidateFuel candidate current))
 := by
  rcases head_cases actual with same | ⟨middle,step,remaining⟩
  · cases same
  · cases step with
    | body_rows ordinary =>
        obtain ⟨skipped,original,parented,rest,rowBefore,afterParent,start,slot,childFuel,combined,
          earlier,child,split,cut,parent,combinedAt,live,previous,selected,tail⟩ := rows_first _ remaining
        have ownerSplit : ownerRows = skipped ++ original :: rest :=
          (congrArg nodeEdges ordinary).trans split
        have entered := Reached.snoc (Reached.refl _) (SourceCurrentOuterExecutionAncestry.Step.body_rows ordinary)
        exact ⟨skipped,original,parented,rest,rowBefore,afterParent,start,slot,childFuel,combined,
          earlier,child,ownerSplit,entered.trans cut,parent,combinedAt,live,previous,selected,tail⟩

end MicroCFTA.SourceCurrentOuterOwnerPrefix
