import MicroCFTA.SourceCurrentConjunctionSharedWorklistStep
import MicroCFTA.HeightOrder

/-!
# Finite coefficient weights for the shared worklist

The vector has one fixed length from the original tuple budget. A row task
uses its stored credit. Appending credits preserves an old queue only when
each old row handle has a credit. These laws concern rank algebra only.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedWorklistWeight
open SourceCurrentConjunctionSharedWorklistStep

variable {Symbol Formula : Type}

/-- Ordinary tasks use level zero. A present row uses its credit plus one. -/
def taskWeight (credits : List Nat) : Task Symbol Formula → Nat → Nat
  | .nodes _, index => if index = 0 then 1 else 0
  | .requirements handles, index => if index = 0 then handles.length + 1 else 0
  | .rows handle, index =>
      match credits[handle]? with
      | none => 0
      | some credit => if index = credit + 1 then 1 else 0

/-- Sum task coefficients without restricting the lower coefficients. -/
def weight (credits : List Nat) : List (Task Symbol Formula) → Nat → Nat
  | [], _ => 0
  | task :: rest, index => taskWeight credits task index + weight credits rest index

/-- Levels zero through the original budget plus one have fixed indices. -/
def rank (budget : Nat) (credits : List Nat) (pending : List (Task Symbol Formula)) :
    Fin (budget + 2) → Nat := fun index => weight credits pending index.val

/-- Every old row task has a present credit before a credit extension. -/
def RowsPresent (credits : List Nat) (pending : List (Task Symbol Formula)) : Prop :=
  ∀ handle, Task.rows handle ∈ pending → ∃ credit, credits[handle]? = some credit

/-- Queue concatenation adds coefficients at each level. -/
theorem weight_append (credits : List Nat) (first last : List (Task Symbol Formula)) (index : Nat) :
    weight credits (first ++ last) index = weight credits first index + weight credits last index := by
  induction first with
  | nil => simp only [List.nil_append, weight, Nat.zero_add]
  | cons task rest ih => simp only [List.cons_append, weight, ih, Nat.add_assoc]

private theorem append_lookup {credits : List Nat} (added : List Nat)
    {handle credit : Nat} (found : credits[handle]? = some credit) :
    (credits ++ added)[handle]? = some credit := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
  exact found

/-- New credits cannot change weights of old tasks with present row handles. -/
theorem weight_append_credits (credits added : List Nat) (pending : List (Task Symbol Formula))
    (present : RowsPresent credits pending) :
    weight (credits ++ added) pending = weight credits pending := by
  funext index
  induction pending with
  | nil => rfl
  | cons task rest ih =>
      have tailPresent : RowsPresent credits rest := by
        intro handle member
        exact present handle (List.mem_cons_of_mem _ member)
      have sameTask : taskWeight (credits ++ added) task index = taskWeight credits task index := by
        cases task with
        | nodes values => rfl
        | requirements handles => rfl
        | rows handle =>
            obtain ⟨credit, found⟩ := present handle List.mem_cons_self
            simp only [taskWeight, found, append_lookup added found]
      simp only [weight, sameTask, ih tailPresent]

/-- The fixed queue-vector order is well-founded for any credit list. -/
theorem wellFounded (budget : Nat) (credits : List Nat) :
    WellFounded (fun first last : List (Task Symbol Formula) =>
      HeightOrder.VectorBelow (budget + 2) (rank budget credits first) (rank budget credits last)) :=
  InvImage.wf (rank budget credits) (HeightOrder.vector_wellFounded (budget + 2))

/-- A local coefficient decrease remains strict inside an unchanged queue frame. -/
theorem replace_decreases (budget : Nat) (credits : List Nat)
    (front suffix first last : List (Task Symbol Formula)) (level : Fin (budget + 2))
    (strict : weight credits first level.val < weight credits last level.val)
    (higher : ∀ index : Fin (budget + 2), level.val < index.val →
      weight credits first index.val ≤ weight credits last index.val) :
    HeightOrder.VectorBelow (budget + 2)
      (rank budget credits (front ++ first ++ suffix))
      (rank budget credits (front ++ last ++ suffix)) := by
  apply HeightOrder.vector_decreases (budget + 2) _ _ level
  · change weight credits (front ++ first ++ suffix) level.val <
      weight credits (front ++ last ++ suffix) level.val
    simp only [weight_append]
    omega
  · intro index above
    change weight credits (front ++ first ++ suffix) index.val ≤
      weight credits (front ++ last ++ suffix) index.val
    have localBound := higher index above
    simp only [weight_append]
    omega

/-- Removing a conjunction task strictly decreases level zero. -/
theorem nodes_removed (budget : Nat) (credits : List Nat) (nodes)
    (front suffix : List (Task Symbol Formula)) :
    HeightOrder.VectorBelow (budget + 2)
      (rank budget credits (front ++ suffix))
      (rank budget credits (front ++ Task.nodes nodes :: suffix)) := by
  have localStep := replace_decreases budget credits front suffix [] [.nodes nodes]
    ⟨0, by omega⟩ (by change 0 < 1 + 0; omega)
    (by intro index _; exact Nat.zero_le _)
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using localStep

/-- An empty requirement task still has one unit to remove. -/
theorem requirements_nil_removed (budget : Nat) (credits : List Nat)
    (front suffix : List (Task Symbol Formula)) :
    HeightOrder.VectorBelow (budget + 2)
      (rank budget credits (front ++ suffix))
      (rank budget credits (front ++ Task.requirements [] :: suffix)) := by
  have localStep := replace_decreases budget credits front suffix [] [.requirements []]
    ⟨0, by omega⟩ (by change 0 < 1 + 0; omega)
    (by intro index _; exact Nat.zero_le _)
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using localStep

/-- Finishing one forced requirement removes one unit at level zero. -/
theorem requirement_removed (budget : Nat) (credits : List Nat) (handle : Nat) (handles : List Nat)
    (front suffix : List (Task Symbol Formula)) :
    HeightOrder.VectorBelow (budget + 2)
      (rank budget credits (front ++ Task.requirements handles :: suffix))
      (rank budget credits (front ++ Task.requirements (handle :: handles) :: suffix)) := by
  have localStep := replace_decreases budget credits front suffix
    [.requirements handles] [.requirements (handle :: handles)] ⟨0, by omega⟩
    (by change handles.length + 1 + 0 < (handles.length + 1) + 1 + 0; omega)
    (by
      intro index above
      change 0 < index.val at above
      have nonzero : index.val ≠ 0 := by omega
      simp only [weight, taskWeight, ite_eq_right nonzero]
      omega)
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using localStep

/-- Removing a present row task decreases its own level. -/
theorem rows_removed (budget : Nat) (credits : List Nat) (handle credit : Nat)
    (front suffix : List (Task Symbol Formula))
    (found : credits[handle]? = some credit) (bounded : credit ≤ budget) :
    HeightOrder.VectorBelow (budget + 2)
      (rank budget credits (front ++ suffix))
      (rank budget credits (front ++ Task.rows handle :: suffix)) := by
  have localStep := replace_decreases budget credits front suffix [] [.rows handle]
    ⟨credit + 1, by omega⟩
    (by
      change 0 < taskWeight credits (.rows handle) (credit + 1) + 0
      have coefficient : taskWeight credits (Task.rows handle : Task Symbol Formula) (credit + 1) = 1 := by
        change (match credits[handle]? with
          | none => 0
          | some value => if credit + 1 = value + 1 then 1 else 0) = 1
        rw [found]
        exact ite_eq_left rfl
      rw [coefficient]
      omega)
    (by intro index _; exact Nat.zero_le _)
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using localStep

/-- A live row can add any finite requirement list and a lower-credit tail. -/
theorem rows_live (budget : Nat) (credits : List Nat) (handle tail credit nextCredit : Nat)
    (handles : List Nat) (front suffix : List (Task Symbol Formula))
    (found : credits[handle]? = some credit) (bounded : credit ≤ budget)
    (tailFound : credits[tail]? = some nextCredit) (smaller : nextCredit < credit) :
    HeightOrder.VectorBelow (budget + 2)
      (rank budget credits (front ++ Task.requirements handles :: Task.rows tail :: suffix))
      (rank budget credits (front ++ Task.rows handle :: suffix)) := by
  have localStep := replace_decreases budget credits front suffix
    [.requirements handles, .rows tail] [.rows handle] ⟨credit + 1, by omega⟩
    (by
      have nonzero : credit + 1 ≠ 0 := by omega
      have different : credit + 1 ≠ nextCredit + 1 := by omega
      have ownCoefficient : taskWeight credits (Task.rows handle : Task Symbol Formula) (credit + 1) = 1 := by
        change (match credits[handle]? with
          | none => 0
          | some value => if credit + 1 = value + 1 then 1 else 0) = 1
        rw [found]
        exact ite_eq_left rfl
      have tailCoefficient : taskWeight credits (Task.rows tail : Task Symbol Formula) (credit + 1) = 0 := by
        change (match credits[tail]? with
          | none => 0
          | some value => if credit + 1 = value + 1 then 1 else 0) = 0
        rw [tailFound]
        exact ite_eq_right different
      have requirementCoefficient :
          taskWeight credits (Task.requirements handles : Task Symbol Formula) (credit + 1) = 0 := by
        change (if credit + 1 = 0 then handles.length + 1 else 0) = 0
        exact ite_eq_right nonzero
      change taskWeight credits (.requirements handles) (credit + 1) +
        (taskWeight credits (.rows tail) (credit + 1) + 0) <
        taskWeight credits (.rows handle) (credit + 1) + 0
      rw [ownCoefficient, tailCoefficient, requirementCoefficient]
      omega)
    (by
      intro index above
      change credit + 1 < index.val at above
      have nonzero : index.val ≠ 0 := by omega
      have different : index.val ≠ nextCredit + 1 := by omega
      have ownDifferent : index.val ≠ credit + 1 := by omega
      simp only [weight, taskWeight, found, tailFound, ite_eq_right nonzero,
        ite_eq_right different, ite_eq_right ownDifferent]
      omega)
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using localStep

/-- Credit extension preserves the old frame when all its row handles are present. -/
theorem rows_live_append (budget : Nat) (credits added : List Nat) (handle tail credit nextCredit : Nat)
    (handles : List Nat) (front suffix : List (Task Symbol Formula))
    (found : credits[handle]? = some credit) (bounded : credit ≤ budget)
    (tailFound : (credits ++ added)[tail]? = some nextCredit) (smaller : nextCredit < credit)
    (present : RowsPresent credits (front ++ Task.rows handle :: suffix)) :
    HeightOrder.VectorBelow (budget + 2)
      (rank budget (credits ++ added) (front ++ Task.requirements handles :: Task.rows tail :: suffix))
      (rank budget credits (front ++ Task.rows handle :: suffix)) := by
  have localStep := rows_live budget (credits ++ added) handle tail credit nextCredit handles front suffix
    (append_lookup added found) bounded tailFound smaller
  have sameRank : rank budget (credits ++ added) (front ++ Task.rows handle :: suffix) =
      rank budget credits (front ++ Task.rows handle :: suffix) := by
    funext index
    exact congrFun (weight_append_credits credits added _ present) index.val
  rw [sameRank] at localStep
  exact localStep

end MicroCFTA.SourceCurrentConjunctionSharedWorklistWeight
