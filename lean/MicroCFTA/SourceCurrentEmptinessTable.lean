import MicroCFTA.SourceEmptinessTaskTableReadback

/-!
# Current open-input checks for conservative emptiness

The source checks openness before table membership. A completed exploration
stores only closed requirements. Its current fixed-point loop therefore
agrees with the earlier table algorithm. This module does not transfer lazy
row demand or machine integer identities.
-/
namespace MicroCFTA.SourceCurrentEmptinessTable
open ConservativeEmptinessExplore

/-- The current exploration guard tests closure before the existing-key test. -/
def skip (budget : Nat) (seen : Table) (key : Int) (closed : Bool) : Bool :=
  budget == 0 || !closed || (lookup key seen).isSome

/-- Reordering completed Boolean tests retains the earlier exploration decision. -/
theorem skip_eq (budget : Nat) (seen : Table) (key : Int) (closed : Bool) :
    skip budget seen key closed = ConservativeEmptinessExplore.skip budget seen key closed := by
  simp only [skip, ConservativeEmptinessExplore.skip]
  cases budget == 0 <;> cases closed <;> cases (lookup key seen).isSome <;> rfl

/-- An open requirement remains possible even when its key occurs in the table. -/
def canAccept (table : Table) (known : Int → Bool) : Item → Bool
  | .empty => false
  | .resident key closed => !closed || ConservativeEmptinessTable.rawCanAccept table known (.resident key closed)

/-- Every requirement read from an actual stored row is closed or empty. -/
def ClosedItem : Item → Prop
  | .empty => True
  | .resident _ closed => closed = true

/-- Closure is required only for rows returned by an actual lookup. -/
def ClosedTable (table : Table) : Prop :=
  ∀ key rows, lookup key table = some rows → ∀ row ∈ rows, ∀ item ∈ row, ClosedItem item

/-- The current requirement check agrees with the earlier check on closed items. -/
theorem canAccept_eq (table : Table) (known : Int → Bool) (item : Item) (closed : ClosedItem item) :
    canAccept table known item = ConservativeEmptinessTable.rawCanAccept table known item := by
  cases item with
  | empty => rfl
  | resident key flag => simp only [ClosedItem] at closed; simp only [canAccept, closed, Bool.not_true, Bool.false_or]

/-- The open-input branch returns true without reading membership or the known set. -/
theorem canAccept_open (table : Table) (known : Int → Bool) (key : Int) :
    canAccept table known (.resident key false) = true := rfl

/-- Openness changes an already stored unknown requirement from false to true. -/
theorem open_present (table : Table) (known : Int → Bool) (key : Int) (rows : Rows)
    (found : lookup key table = some rows) (unknown : known key = false) :
    canAccept table known (.resident key false) = true ∧
      ConservativeEmptinessTable.rawCanAccept table known (.resident key false) = false := by
  exact ⟨rfl, by simp only [ConservativeEmptinessTable.rawCanAccept, found, unknown]⟩

/-- One synchronous round uses the current open-input check in original row order. -/
def step (table : Table) (known : Int → Bool) (key : Int) : Bool :=
  match lookup key table with
  | none => false
  | some rows => rows.any (fun row => row.all (canAccept table known))

private theorem all_eq (table : Table) (known : Int → Bool) (row : List Item)
    (closed : ∀ item ∈ row, ClosedItem item) :
    row.all (canAccept table known) = row.all (ConservativeEmptinessTable.rawCanAccept table known) := by
  induction row with
  | nil => rfl
  | cons item rest ih =>
      simp only [List.all_cons, canAccept_eq table known item (closed item List.mem_cons_self),
        ih (fun item member => closed item (List.mem_cons_of_mem _ member))]

private theorem any_eq (table : Table) (known : Int → Bool) (rows : Rows)
    (closed : ∀ row ∈ rows, ∀ item ∈ row, ClosedItem item) :
    rows.any (fun row => row.all (canAccept table known)) =
      rows.any (fun row => row.all (ConservativeEmptinessTable.rawCanAccept table known)) := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      simp only [List.any_cons, all_eq table known row (closed row List.mem_cons_self),
        ih (fun row member => closed row (List.mem_cons_of_mem _ member))]

/-- Actual closed stored rows give the earlier exact synchronous operator. -/
theorem step_eq (table : Table) (closed : ClosedTable table) (known : Int → Bool) :
    step table known = ConservativeEmptinessTable.rawStep table known := by
  funext key
  cases found : lookup key table with
  | none => simp only [step, ConservativeEmptinessTable.rawStep, found]
  | some rows =>
      simp only [step, ConservativeEmptinessTable.rawStep, found]
      exact any_eq table known rows (closed key rows found)

/-- The current equality-stop loop uses the same finite key equality test. -/
def grow (table : Table) : Nat → (Int → Bool) → Option (Int → Bool)
  | 0, _ => none
  | fuel + 1, known =>
      let next := step table known
      if ConservativeEmptinessTable.same table next known then some known else grow table fuel next

/-- Every current completed loop agrees with the earlier loop on actual closed rows. -/
theorem grow_eq (table : Table) (closed : ClosedTable table) (fuel : Nat) (known : Int → Bool) :
    grow table fuel known = ConservativeEmptinessTable.grow table fuel known := by
  induction fuel generalizing known with
  | zero => rfl
  | succ fuel ih => simp only [grow, ConservativeEmptinessTable.grow, step_eq table closed, ih]

/-- Encoding an actually closed value produces a closed table requirement. -/
theorem encode_closed (value : InternedConstructorTemplates.Value
    (SourceObservations.Label FullSyntax.Formula) (SourceSymbolicIndex.Constraint FullSyntax.Formula))
    (closed : value.free = []) : ClosedItem (SourceEmptinessTaskTrace.encode value) := by
  unfold SourceEmptinessTaskTrace.encode
  cases SourceEmptinessKeys.key value <;> simp only [ClosedItem, closed, List.isEmpty_nil] <;> trivial

/-- Actual empty-start task exploration derives closure of every returned table row. -/
theorem table_closed [DecidableEq (SourceObservations.Label FullSyntax.Formula)]
    [DecidableEq (InternedConstructorTemplates.EdgeKey (SourceObservations.Label FullSyntax.Formula)
      (SourceSymbolicIndex.Constraint FullSyntax.Formula))]
    {emptyGuard : SourceSymbolicIndex.Constraint FullSyntax.Formula} {conjoin}
    (trace : SourceEmptinessTaskTrace.Run (width := width) emptyGuard conjoin budget [] pending before entries after)
    (ready : SourceEmptinessTasks.Ready emptyGuard conjoin before) :
    ClosedTable (SourceEmptinessTaskTrace.table after entries) := by
  intro key rows found
  rw [SourceEmptinessTaskTableReadback.lookup_table] at found
  cases original : DelayedEmptinessExplore.lookup key entries with
  | none => simp only [original, Option.map_none] at found; cases found
  | some entry =>
      simp only [original, Option.map_some, Option.some.injEq] at found
      subst rows
      intro row member item selected
      obtain ⟨tasks, tasksMember, rfl⟩ := List.mem_map.mp member
      obtain ⟨task, taskMember, rfl⟩ := List.mem_map.mp selected
      have complete := SourceEmptinessTaskTrace.rows_complete trace ready key entry original task
        (List.mem_flatten.mpr ⟨tasks, tasksMember, taskMember⟩)
      obtain ⟨value, _, _, closed, actual⟩ := SourceEmptinessTaskTrace.readItem_complete complete
      rw [actual]
      exact encode_closed value closed

end MicroCFTA.SourceCurrentEmptinessTable
