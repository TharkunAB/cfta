import MicroCFTA.SourceCurrentStoredLiteralRowLineage

/-!
# Indexed first ordinary-child cuts

The actual leaf traversal stops at a closed value. An open union or Mu
retains the exact prefix before its first ordinary child crossing. The cut
records the selected row, child, remaining leaf index and original offsets.
-/
namespace MicroCFTA.SourceCurrentIndexedFirstOrdinaryCut
open Cache InternedConstructorTemplates
open InternedStoredSubstitution (leaves manyLeaves edgeLeaves)
open SourceCurrentStoredLiteralRowLineage (RowAt)
variable {Symbol Guard : Type}

private theorem flat_lookup (f : α → List β) (values : List α) (index : Nat) (value : β)
    (found : (values.flatMap f)[index]? = some value) :
    ∃ outer selected inner,
      values[outer]? = some selected ∧ (f selected)[inner]? = some value ∧
      index = ((values.take outer).flatMap f).length + inner := by
  induction values generalizing index with
  | nil => simp only [List.flatMap_nil,List.getElem?_nil] at found; cases found
  | cons first rest ih =>
      simp only [List.flatMap_cons] at found
      by_cases short : index < (f first).length
      · rw [List.getElem?_append_left short] at found
        exact ⟨0,first,index,rfl,found,by simp only [List.take_zero,List.flatMap_nil,List.length_nil,Nat.zero_add]⟩
      · have long : (f first).length ≤ index := by omega
        rw [List.getElem?_append_right long] at found
        obtain ⟨outer,selected,inner,source,inside,offset⟩ := ih (index - (f first).length) found
        refine ⟨outer + 1,selected,inner,source,inside,?_⟩
        simp only [List.take_succ_cons,List.flatMap_cons,List.length_append]
        omega

private theorem many_flat (values : List (Value Symbol Guard)) :
    manyLeaves values = values.flatMap leaves := by
  induction values with
  | nil => simp only [manyLeaves,List.flatMap_nil]
  | cons first rest ih => simp only [manyLeaves,List.flatMap_cons,ih]

private theorem edges_flat (rows : List (EdgeValue Symbol Guard)) :
    edgeLeaves rows = rows.flatMap (fun row => manyLeaves row.children) := by
  induction rows with
  | nil => simp only [edgeLeaves,List.flatMap_nil]
  | cons row rest ih =>
      cases row
      simp only [edgeLeaves,EdgeValue.children,List.flatMap_cons,ih]

/-- One indexed traversal reaches its first ordinary child after only union and Mu prefixes. -/
inductive Cut : Value Symbol Guard → Nat → Value Symbol Guard →
    EdgeValue Symbol Guard → Nat → Value Symbol Guard → Nat → Prop where
  /-- An open ordinary value supplies the exact row, child and two leaf offsets. -/
  | node {entry rows depth free index leaf outputIndex row childIndex child inner}
      (opened : free ≠ [])
      (selected : rows[outputIndex]? = some row)
      (chosen : row.children[childIndex]? = some child)
      (found : (leaves child)[inner]? = some leaf)
      (offset : index = (edgeLeaves (rows.take outputIndex)).length +
        (manyLeaves (row.children.take childIndex)).length + inner) :
      Cut (.node entry rows depth free) index leaf row childIndex child inner
  /-- An open union retains its exact selected member and prefix leaf count. -/
  | union {entry members depth free index leaf memberIndex member memberLeafIndex row childIndex child inner}
      (opened : free ≠ [])
      (selected : members[memberIndex]? = some member)
      (offset : index = (manyLeaves (members.take memberIndex)).length + memberLeafIndex)
      (nested : Cut member memberLeafIndex leaf row childIndex child inner) :
      Cut (.union entry members depth free) index leaf row childIndex child inner
  /-- An open Mu retains the same index in its actual stored body. -/
  | mu {entry body depth ordinary index leaf row childIndex child inner}
      (opened : (Value.mu entry body depth ordinary).free ≠ [])
      (nested : Cut body index leaf row childIndex child inner) :
      Cut (.mu entry body depth ordinary) index leaf row childIndex child inner

/-- Every cut derives its full parent row and exact child and inner leaf lookups. -/
theorem Cut.facts {value : Value Symbol Guard} {index leaf row childIndex child inner}
    (cut : Cut value index leaf row childIndex child inner) :
    RowAt value row ∧ row.children[childIndex]? = some child ∧ (leaves child)[inner]? = some leaf := by
  induction cut with
  | node _ selected chosen found _ => exact ⟨.node selected,chosen,found⟩
  | union _ selected _ _ ih => exact ⟨.union selected ih.1,ih.2⟩
  | mu _ _ ih => exact ⟨.mu ih.1,ih.2⟩

/-- An actual row-bearing leaf has a root structural row or an indexed first ordinary-child cut. -/
theorem split (value : Value Symbol Guard) (index : Nat) (leaf : Value Symbol Guard)
    (found : (leaves value)[index]? = some leaf)
    (row : EdgeValue Symbol Guard) (inside : RowAt leaf row) :
    RowAt value row ∨ ∃ parentRow childIndex child inner,
      Cut value index leaf parentRow childIndex child inner := by
  generalize measure : sizeOf value = bound
  induction bound using Nat.strongRecOn generalizing value index with
  | ind bound ih =>
    by_cases closed : value.free = []
    · have lookup : ([value] : List (Value Symbol Guard))[index]? = some leaf := by
        simpa only [leaves.eq_def,closed,List.isEmpty_nil,↓reduceIte] using found
      cases index with
      | zero =>
        have same : value = leaf := Option.some.inj lookup
        exact .inl (same.symm ▸ inside)
      | succ index => simp only [List.getElem?_cons_succ,List.getElem?_nil] at lookup; cases lookup
    · cases value with
      | empty => exact False.elim (closed rfl)
      | reference name =>
        rw [leaves.eq_def] at found
        simp only [Value.free,List.isEmpty_cons,Bool.false_eq_true,↓reduceIte] at found
        cases index with
        | zero =>
          have same : Value.reference name = leaf := Option.some.inj found
          rw [← same] at inside
          cases inside
        | succ index => simp only [List.getElem?_cons_succ,List.getElem?_nil] at found; cases found
      | node entry rows depth free =>
        change free ≠ [] at closed
        have leafRows : leaves (.node entry rows depth free : Value Symbol Guard) = edgeLeaves rows := by
          rw [leaves.eq_def]
          simp only [Value.free,List.isEmpty_eq_false_iff.mpr closed,Bool.false_eq_true,↓reduceIte]
        rw [leafRows,edges_flat] at found
        obtain ⟨outputIndex,parentRow,rowInner,selected,rowFound,rowOffset⟩ :=
          flat_lookup (fun parent : EdgeValue Symbol Guard => manyLeaves parent.children) rows index leaf found
        rw [many_flat] at rowFound
        obtain ⟨childIndex,child,inner,chosen,childFound,childOffset⟩ :=
          flat_lookup leaves parentRow.children rowInner leaf rowFound
        refine .inr ⟨parentRow,childIndex,child,inner,.node closed selected chosen childFound ?_⟩
        rw [← edges_flat] at rowOffset
        rw [← many_flat] at childOffset
        omega
      | union entry members depth free =>
        change free ≠ [] at closed
        have leafMembers : leaves (.union entry members depth free : Value Symbol Guard) = manyLeaves members := by
          rw [leaves.eq_def]
          simp only [Value.free,List.isEmpty_eq_false_iff.mpr closed,Bool.false_eq_true,↓reduceIte]
        rw [leafMembers,many_flat] at found
        obtain ⟨memberIndex,member,memberLeafIndex,selected,memberFound,offset⟩ :=
          flat_lookup leaves members index leaf found
        have smaller : sizeOf member < bound := by
          have small := List.sizeOf_lt_of_mem (List.mem_of_getElem? selected)
          simp only [Value.union.sizeOf_spec] at measure
          omega
        have nested := ih (sizeOf member) smaller member memberLeafIndex memberFound rfl
        rcases nested with part | ⟨parentRow,childIndex,child,inner,cut⟩
        · exact .inl (.union selected part)
        · refine .inr ⟨parentRow,childIndex,child,inner,.union closed selected ?_ cut⟩
          simpa only [many_flat] using offset
      | mu entry body depth ordinary =>
        have leafBody : leaves (.mu entry body depth ordinary) = leaves body := by
          rw [leaves.eq_def]
          simp only [List.isEmpty_eq_false_iff.mpr closed,Bool.false_eq_true,↓reduceIte]
        rw [leafBody] at found
        have smaller : sizeOf body < bound := by
          simp only [Value.mu.sizeOf_spec] at measure
          omega
        have nested := ih (sizeOf body) smaller body index found rfl
        rcases nested with part | ⟨parentRow,childIndex,child,inner,cut⟩
        · exact .inl (.mu part)
        · exact .inr ⟨parentRow,childIndex,child,inner,.mu closed cut⟩

end MicroCFTA.SourceCurrentIndexedFirstOrdinaryCut

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.SourceCurrentIndexedFirstOrdinaryCut.Cut
#print MicroCFTA.SourceCurrentIndexedFirstOrdinaryCut.Cut
#print axioms MicroCFTA.SourceCurrentIndexedFirstOrdinaryCut.Cut

#check @MicroCFTA.SourceCurrentIndexedFirstOrdinaryCut.Cut.facts
#print MicroCFTA.SourceCurrentIndexedFirstOrdinaryCut.Cut.facts
#print axioms MicroCFTA.SourceCurrentIndexedFirstOrdinaryCut.Cut.facts

#check @MicroCFTA.SourceCurrentIndexedFirstOrdinaryCut.split
#print MicroCFTA.SourceCurrentIndexedFirstOrdinaryCut.split
#print axioms MicroCFTA.SourceCurrentIndexedFirstOrdinaryCut.split

