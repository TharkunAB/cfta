import MicroCFTA.SourceTypingHelperOrder

/-!
# Relevant helper declaration discovery

The source restricts declaration discovery to a finite set of constructor
types from the completed typing rows. The walk still emits a fresh row before
its fields. It stops at every irrelevant algebraic type. This finite inventory
bounds the walk even if the description function has infinitely many keys.
Generic metadata, label encoding, and machine integer bounds remain separate.
-/
namespace MicroCFTA.SourceTypingRelevantHelperOrder

open Generic
variable {State Constructor : Type}

/-- Count the finite needed inventory that the walk has not visited. -/
def unseen [DecidableEq State] (needed seen : List State) : List State :=
  needed.filter fun state => decide (state ∉ seen)

private theorem unseen_insert [DecidableEq State] (needed seen : List State) (state : State) :
    unseen needed (state :: seen) = (unseen needed seen).filter fun key => decide (key ≠ state) := by
  simp only [unseen, List.filter_filter]
  apply List.filter_congr
  intro key _
  simp

private theorem unseen_decreases [DecidableEq State] (needed seen : List State) (state : State)
    (relevant : state ∈ needed) (fresh : state ∉ seen) :
    (unseen needed (state :: seen)).length < (unseen needed seen).length := by
  rw [unseen_insert]
  have member : state ∈ unseen needed seen := by simp [unseen, relevant, fresh]
  have bound := List.length_filter_le (fun key => decide (key ≠ state)) (unseen needed seen)
  apply Nat.lt_of_le_of_ne bound
  intro equal
  have excluded := List.length_filter_eq_length_iff.mp equal state member
  simp at excluded

/-- Execute the source walk with its finite needed-type set and exact source order. -/
def reachable [DecidableEq State] (describe : State → Description State Constructor)
    (needed seen : List State) (pending : List State) : List (Row State Constructor) :=
  match pending with
  | [] => []
  | state :: rest =>
      match describe state with
      | .atomic => reachable describe needed seen rest
      | .algebraic alternatives =>
          if _blocked : state ∉ needed ∨ state ∈ seen then
            reachable describe needed seen rest
          else alternatives :: reachable describe needed (state :: seen) (children alternatives ++ rest)
termination_by ((unseen needed seen).length, pending.length)
decreasing_by
  · exact Prod.Lex.right _ (by simp)
  · exact Prod.Lex.right _ (by simp)
  · apply Prod.Lex.left
    exact unseen_decreases needed seen state (by simp_all) (by simp_all)

/-- The repaired operational walk stops before any irrelevant type's fields. -/
inductive Reachable (describe : State → Description State Constructor) (needed : List State) :
    List State → List State → List (Row State Constructor) → Prop where
  | nil : Reachable describe needed seen [] []
  | atomic (actual : describe state = .atomic)
      (tail : Reachable describe needed seen pending rows) :
      Reachable describe needed seen (state :: pending) rows
  | blocked (actual : describe state = .algebraic alternatives)
      (skip : state ∉ needed ∨ state ∈ seen)
      (tail : Reachable describe needed seen pending rows) :
      Reachable describe needed seen (state :: pending) rows
  | fresh (actual : describe state = .algebraic alternatives)
      (relevant : state ∈ needed) (new : state ∉ seen)
      (tail : Reachable describe needed (state :: seen) (children alternatives ++ pending) rows) :
      Reachable describe needed seen (state :: pending) (alternatives :: rows)

/-- The finite computation derives a completed trace without a discovery oracle. -/
theorem reachable_trace [DecidableEq State] (describe : State → Description State Constructor)
    (needed seen pending : List State) :
    Reachable describe needed seen pending (reachable describe needed seen pending) := by
  induction seen, pending using reachable.induct describe needed with
  | case1 seen => simpa only [reachable] using (Reachable.nil (describe := describe) (needed := needed) (seen := seen))
  | case2 seen state rest actual ih =>
      simpa only [reachable, actual] using Reachable.atomic actual ih
  | case3 seen state rest alternatives actual blocked ih =>
      simpa only [reachable, actual, dite_eq_left blocked] using Reachable.blocked actual blocked ih
  | case4 seen state rest alternatives actual fresh ih =>
      have relevant : state ∈ needed := by simp_all
      have new : state ∉ seen := by simp_all
      simpa only [reachable, actual, dite_eq_right fresh] using Reachable.fresh actual relevant new ih

/-- Every emitted row is an original declaration of a needed type. -/
theorem Reachable.rows_relevant {describe : State → Description State Constructor}
    {needed seen pending rows} (trace : Reachable describe needed seen pending rows) :
    ∀ row ∈ rows, ∃ state ∈ needed, describe state = .algebraic row := by
  induction trace with
  | nil => simp
  | atomic _ _ ih => exact ih
  | blocked _ _ _ ih => exact ih
  | fresh actual relevant _ _ ih =>
      intro row member
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨_, relevant, actual⟩
      · exact ih row later

/-- Each emitted algebraic row consumes an unvisited needed-type occurrence. -/
theorem Reachable.length_bound [DecidableEq State]
    {describe : State → Description State Constructor} {needed seen pending rows}
    (trace : Reachable describe needed seen pending rows) :
    rows.length ≤ (unseen needed seen).length := by
  induction trace with
  | nil => simp
  | atomic _ _ ih => exact ih
  | blocked _ _ _ ih => exact ih
  | fresh _ relevant new _ ih =>
      have decrease := unseen_decreases _ _ _ relevant new
      simp only [List.length_cons]
      omega

/-- The actual computation emits at most the finite inventory's unvisited count. -/
theorem reachable_length [DecidableEq State] (describe : State → Description State Constructor)
    (needed seen pending : List State) :
    (reachable describe needed seen pending).length ≤ (unseen needed seen).length :=
  (reachable_trace describe needed seen pending).length_bound

/-- Compute declaration positions from the repaired finite walk. -/
def positions [DecidableEq State] (label : Constructor → String)
    (describe : State → Description State Constructor) (needed roots : List State) :
    Cache.Table String Int :=
  SourceTypingHelperOrder.positions label (reachable describe needed [] roots)

/-- The returned map uses the last original emitted occurrence of each label. -/
theorem positions_last [DecidableEq State] (label : Constructor → String)
    (describe : State → Description State Constructor) (needed roots : List State) (key : String) :
    positions label describe needed roots key =
      (((SourceTypingHelperOrder.entries label (reachable describe needed [] roots)).filter
        fun pair => decide (pair.1 = key)).getLast?).map Prod.snd :=
  SourceTypingHelperOrder.positions_last label (reachable describe needed [] roots) key

/-- Every returned position is the local index of an actual needed declaration. -/
theorem position_origin [DecidableEq State] (label : Constructor → String)
    (describe : State → Description State Constructor) (needed roots : List State)
    (key : String) (position : Int) (found : positions label describe needed roots key = some position) :
    ∃ state ∈ needed, ∃ row, ∃ (constructor : Constructor) (fields : List State) (index : Nat),
      describe state = .algebraic row ∧ row[index]? = some (constructor, fields) ∧
        label constructor = key ∧ (index : Int) = position := by
  obtain ⟨row, reached, constructor, fields, index, declared, name, offset⟩ :=
    SourceTypingHelperOrder.position_origin label (reachable describe needed [] roots) key position found
  obtain ⟨state, relevant, actual⟩ :=
    (reachable_trace describe needed [] roots).rows_relevant row reached
  exact ⟨state, relevant, row, constructor, fields, index, actual, declared, name, offset⟩

/-- The source order uses the computed position and the original label. -/
def order [DecidableEq State] (label : Constructor → String)
    (describe : State → Description State Constructor) (needed roots : List State)
    (symbol : String) : Int × String := ((positions label describe needed roots symbol).getD 0, symbol)

/-- Every absent label uses literal zero after the finite repaired walk. -/
theorem order_absent [DecidableEq State] (label : Constructor → String)
    (describe : State → Description State Constructor) (needed roots : List State) (key : String)
    (absent : ∀ position, (key, position) ∉
      SourceTypingHelperOrder.entries label (reachable describe needed [] roots)) :
    order label describe needed roots key = (0, key) :=
  SourceTypingHelperOrder.order_absent label (reachable describe needed [] roots) key absent

end MicroCFTA.SourceTypingRelevantHelperOrder
