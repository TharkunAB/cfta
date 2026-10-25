import MicroCFTA.SourceEndpointMemo

/-!
# Exact answers and retained entries for descendant memo calls

The proof follows each actual lookup and ordered recursive call. It derives
both returned memo invariants from the original coherent physical heap and
available input records. It does not assume future cache correctness.
-/
namespace MicroCFTA.SourceEndpointMemoCorrect
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open SourceObservations SourceSymbolicIndex SourceEndpointMemo
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "source" => SourceMemoGate.unconstrained

/-- A completed call returns the specified Boolean and retains both valid memo histories. -/
structure Checked (heap : State Symbol Guard) (before : Memos) (expected : Bool) (result : Bool × Memos) : Prop where
  answer : result.1 = expected
  valid : SourceEndpointMemo.Valid heap result.2
  keeps : Keeps before result.2

/-- A result without memo effects retains the initial invariants. -/
theorem pure_checked (heap : State Symbol Guard) (memos : Memos) (valid : SourceEndpointMemo.Valid heap memos)
    (answer : Bool) : Checked heap memos answer (answer, memos) := ⟨rfl, valid, keeps_refl memos⟩

/-- Saving the completed root answer preserves all earlier recursive-call results. -/
theorem finish_checked (heap : State Symbol Guard) (before : Memos) (value : Value Symbol Guard)
    (available : Available heap value) (result : Bool × Memos)
    (checked : Checked heap before (SourceEndpointReachability.reaches source value) result) :
    Checked heap before (SourceEndpointReachability.reaches source value)
      (result.1, {result.2 with descendants := save result.2.descendants value result.1}) := by
  refine ⟨checked.answer, ⟨save_correct heap result.2.descendants checked.valid.descendants value available
    result.1 checked.answer, checked.valid.predicate⟩, ?_⟩
  exact keeps_trans checked.keeps ⟨save_extends _ _ _, extends_refl _⟩

mutual
/-- Every actual descendant query returns the concrete source Boolean and two coherent retained memos. -/
theorem run_checked (value : Value Symbol Guard) (heap : State Symbol Guard) (coherent : Coherent heap)
    (available : Available heap value) (memos : Memos) (valid : SourceEndpointMemo.Valid heap memos) :
    Checked heap memos (SourceEndpointReachability.reaches source value) (SourceEndpointMemo.run value memos) := by
  cases found : memos.descendants value.referenceOf with
  | some pair =>
      rcases pair with ⟨original, answer⟩
      obtain ⟨identity, resident, actual⟩ := valid.descendants _ original answer found
      have same := InternedFreshProbeKeys.resident_reference_injective heap coherent original value
        resident.resident available.resident identity
      subst original
      have checked : Checked heap memos (SourceEndpointReachability.reaches source value) (answer, memos) :=
        ⟨actual, valid, keeps_refl memos⟩
      rw [SourceEndpointMemo.run.eq_def, found]
      exact checked
  | none =>
      cases value with
      | empty =>
          simpa [SourceEndpointMemo.run, found, SourceEndpointReachability.reaches, Value.depth] using
            finish_checked heap memos .empty available (false, memos)
              (by simpa [SourceEndpointReachability.reaches, Value.depth] using pure_checked heap memos valid false)
      | reference name =>
          simpa [SourceEndpointMemo.run, found, SourceEndpointReachability.reaches, Value.depth] using
            finish_checked heap memos (.reference name) available (false, memos)
              (by simpa [SourceEndpointReachability.reaches, Value.depth] using pure_checked heap memos valid false)
      | mu entry body depth ordinary =>
          have predicate := SourceUnconstrainedMemo.run_exact (.mu entry body depth ordinary) heap coherent
            available memos.predicate valid.predicate
          have checked : Checked heap memos (SourceEndpointReachability.reaches source (.mu entry body depth ordinary))
              (!(SourceUnconstrainedMemo.run (.mu entry body depth ordinary) memos.predicate).1,
                {memos with predicate := (SourceUnconstrainedMemo.run (.mu entry body depth ordinary) memos.predicate).2}) := by
            refine ⟨?_, ⟨valid.descendants, predicate.2⟩, ⟨extends_refl _, predicate_extends _ _⟩⟩
            rw [SourceEndpointReachability.binder, predicate.1]
          simpa [SourceEndpointMemo.run, found, Value.depth] using finish_checked heap memos (.mu entry body depth ordinary)
            available _ checked
      | union entry members depth free =>
          by_cases zero : depth = 0
          · have absent : memos.descendants (Value.union entry members 0 free).referenceOf = none := by
              simpa only [zero] using found
            simpa [SourceEndpointMemo.run, absent, Value.depth, zero, SourceEndpointReachability.reaches] using
              finish_checked heap memos (.union entry members depth free) available (false, memos)
                (by simpa [SourceEndpointReachability.reaches, Value.depth, zero] using pure_checked heap memos valid false)
          · have children : ∀ child ∈ members, Available heap child := available.children
            have checked := many_checked members heap coherent children memos valid
            have result : Checked heap memos (SourceEndpointReachability.reaches source (.union entry members depth free))
                (many members memos) := by simpa [SourceEndpointReachability.reaches, Value.depth, zero] using checked
            simpa [SourceEndpointMemo.run, found, Value.depth, zero] using
              finish_checked heap memos (.union entry members depth free) available _ result
      | node entry edges depth free =>
          by_cases zero : depth = 0
          · have absent : memos.descendants (Value.node entry edges 0 free).referenceOf = none := by
              simpa only [zero] using found
            simpa [SourceEndpointMemo.run, absent, Value.depth, zero, SourceEndpointReachability.reaches] using
              finish_checked heap memos (.node entry edges depth free) available (false, memos)
                (by simpa [SourceEndpointReachability.reaches, Value.depth, zero] using pure_checked heap memos valid false)
          · have children : ∀ edge ∈ edges, ∀ child ∈ edge.children, Available heap child := by
              intro edge member child selected
              exact available.children child (List.mem_flatMap.mpr ⟨edge, member, selected⟩)
            have checked := rows_checked edges heap coherent children memos valid
            have result : Checked heap memos (SourceEndpointReachability.reaches source (.node entry edges depth free))
                (rows edges memos) := by simpa [SourceEndpointReachability.reaches, Value.depth, zero] using checked
            simpa [SourceEndpointMemo.run, found, Value.depth, zero] using
              finish_checked heap memos (.node entry edges depth free) available _ result
termination_by sizeOf value

/-- False children pass the proved current memos to the next actual recursive call. -/
theorem many_checked (values : List (Value Symbol Guard)) (heap : State Symbol Guard) (coherent : Coherent heap)
    (available : ∀ value ∈ values, Available heap value) (memos : Memos) (valid : SourceEndpointMemo.Valid heap memos) :
    Checked heap memos (SourceEndpointReachability.many source values) (many values memos) := by
  cases values with
  | nil => simpa [many, rows, SourceEndpointReachability.many, SourceEndpointReachability.rows] using pure_checked heap memos valid false
  | cons first rest =>
      have head := run_checked first heap coherent (available first (by simp)) memos valid
      cases answer : (SourceEndpointMemo.run first memos).1 with
      | true =>
          have expected : SourceEndpointReachability.reaches source first = true := head.answer.symm.trans answer
          simpa only [many, answer, Bool.true_eq, ↓reduceIte, SourceEndpointReachability.many,
            expected, Bool.true_or] using head
      | false =>
          have expected : SourceEndpointReachability.reaches source first = false := head.answer.symm.trans answer
          have tail := many_checked rest heap coherent (fun value member => available value (by simp [member]))
            (SourceEndpointMemo.run first memos).2 head.valid
          refine ⟨?_, ?_, ?_⟩
          · simpa only [many, answer, Bool.false_eq_true, ↓reduceIte, SourceEndpointReachability.many,
              expected, Bool.false_or] using tail.answer
          · simpa only [many, answer, Bool.false_eq_true, ↓reduceIte] using tail.valid
          · simpa only [many, answer, Bool.false_eq_true, ↓reduceIte] using keeps_trans head.keeps tail.keeps
termination_by sizeOf values

/-- Original row order retains both memo families through every false edge. -/
theorem rows_checked (edges : List (EdgeValue Symbol Guard)) (heap : State Symbol Guard) (coherent : Coherent heap)
    (available : ∀ edge ∈ edges, ∀ child ∈ edge.children, Available heap child)
    (memos : Memos) (valid : SourceEndpointMemo.Valid heap memos) :
    Checked heap memos (SourceEndpointReachability.rows source edges) (rows edges memos) := by
  cases edges with
  | nil => simpa [many, rows, SourceEndpointReachability.many, SourceEndpointReachability.rows] using pure_checked heap memos valid false
  | cons first rest => cases first with
    | mk entry children =>
        have head := many_checked children heap coherent (available (.mk entry children) (by simp)) memos valid
        cases answer : (many children memos).1 with
        | true =>
            have expected : SourceEndpointReachability.many source children = true := head.answer.symm.trans answer
            simpa only [rows, answer, Bool.true_eq, ↓reduceIte, SourceEndpointReachability.rows,
              expected, Bool.true_or] using head
        | false =>
            have expected : SourceEndpointReachability.many source children = false := head.answer.symm.trans answer
            have tail := rows_checked rest heap coherent (fun edge member => available edge (by simp [member]))
              (many children memos).2 head.valid
            refine ⟨?_, ?_, ?_⟩
            · simpa only [rows, answer, Bool.false_eq_true, ↓reduceIte, SourceEndpointReachability.rows,
                expected, Bool.false_or] using tail.answer
            · simpa only [rows, answer, Bool.false_eq_true, ↓reduceIte] using tail.valid
            · simpa only [rows, answer, Bool.false_eq_true, ↓reduceIte] using keeps_trans head.keeps tail.keeps
termination_by sizeOf edges
end

end MicroCFTA.SourceEndpointMemoCorrect
