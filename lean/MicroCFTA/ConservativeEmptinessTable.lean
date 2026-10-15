import MicroCFTA.ConservativeEmptiness
import MicroCFTA.ConservativeEmptinessExplore

/-!
# Finite fixed points from actual explored table keys

The first stored lookup determines each row list. The finite carrier contains
exactly the stored keys. Classification retains row and requirement order.
Missing keys remain possible requirements but are absent from every known set.
The completed list table models logical map reads. It does not model native
`IntMap` or `IntSet` storage, source exposure, or lazy computation of rows.
-/
namespace MicroCFTA.ConservativeEmptinessTable
open ConservativeEmptinessExplore

/-- Only keys stored in the actual finite table enter the fixed-point carrier. -/
abbrev Key (table : Table) := { key : Int // key ∈ table.map Prod.fst }

/-- Attach actual key membership without changing the stored key order. -/
def states (table : Table) : List (Key table) := (table.map Prod.fst).attach

/-- The table itself supplies every member of its finite carrier. -/
theorem states_complete (table : Table) (state : Key table) : state ∈ states table := by
  simp [states]

/-- The finite list has one position for each stored table entry. -/
theorem states_length (table : Table) : (states table).length = table.length := by simp [states]

/-- Classify by actual table membership; the closed bit does not affect fixed-point reads. -/
def classify (table : Table) : Item → ConservativeEmptiness.Requirement (Key table)
  | .empty => .empty
  | .resident key _ => if present : key ∈ table.map Prod.fst then .inside ⟨key, present⟩ else .outside

/-- Empty is false, missing keys are true, and present keys read the current known set. -/
def rawCanAccept (table : Table) (known : Int → Bool) : Item → Bool
  | .empty => false
  | .resident key _ => match lookup key table with
      | none => true
      | some _ => known key

/-- The table operator uses the original rows and marks no absent key. -/
def rawStep (table : Table) (known : Int → Bool) (key : Int) : Bool :=
  match lookup key table with
  | none => false
  | some rows => rows.any (fun row => row.all (rawCanAccept table known))

/-- Restriction forgets only raw keys outside the stored carrier. -/
def restrict (table : Table) (known : Int → Bool) (state : Key table) : Bool := known state.val

/-- Convert each original row in order to the derived finite carrier. -/
def rows (table : Table) (state : Key table) : List (List (ConservativeEmptiness.Requirement (Key table))) :=
  ((lookup state.val table).getD []).map (fun row => row.map (classify table))

/-- Raw and finite requirement classifiers give the same Boolean on every original item. -/
theorem canAccept_agrees (table : Table) (known : Int → Bool) (item : Item) :
    rawCanAccept table known item = ConservativeEmptiness.canAccept (restrict table known) (classify table item) := by
  cases item with
  | empty => rfl
  | resident key closed =>
      by_cases present : key ∈ table.map Prod.fst
      · cases found : lookup key table with
        | none => exact False.elim (((lookup_none_iff key table).mp found) present)
        | some original => simp [rawCanAccept, found, classify, present, ConservativeEmptiness.canAccept, restrict]
      · have absent := (lookup_none_iff key table).mpr present
        simp [rawCanAccept, absent, classify, present, ConservativeEmptiness.canAccept]

/-- Actual lookup rows agree exactly with the finite OR-of-AND operator. -/
theorem step_agrees (table : Table) (known : Int → Bool) (state : Key table) :
    rawStep table known state.val = ConservativeEmptiness.step (rows table) (restrict table known) state := by
  cases found : lookup state.val table with
  | none => exact False.elim ((lookup_none_iff state.val table).mp found state.property)
  | some original =>
      simp only [rawStep, found, ConservativeEmptiness.step, rows, Option.getD_some,
        List.any_map, List.all_map, Function.comp_def]
      simp only [← canAccept_agrees]

/-- Restriction commutes with one complete table step. -/
theorem restrict_step (table : Table) (known : Int → Bool) :
    restrict table (rawStep table known) = ConservativeEmptiness.step (rows table) (restrict table known) :=
  funext (step_agrees table known)

/-- Raw requirement evaluation preserves inclusion. -/
theorem rawCanAccept_monotone (table : Table) (left right : Int → Bool)
    (included : Productivity.Included left right) (item : Item) :
    rawCanAccept table left item = true → rawCanAccept table right item = true := by
  cases item with
  | empty => intro impossible; cases impossible
  | resident key closed =>
      cases found : lookup key table with
      | none => simp [rawCanAccept, found]
      | some original => simpa only [rawCanAccept, found] using included key

/-- The literal table operator is monotone, including missing keys. -/
theorem rawStep_monotone (table : Table) : Productivity.Monotone (rawStep table) := by
  intro left right included key marked
  cases found : lookup key table with
  | none => simp [rawStep, found] at marked
  | some original =>
      simp only [rawStep, found] at marked ⊢
      obtain ⟨row, member, obligations⟩ := List.any_eq_true.mp marked
      apply List.any_eq_true.mpr
      refine ⟨row, member, List.all_eq_true.mpr ?_⟩
      intro item selected
      exact rawCanAccept_monotone table left right included item (List.all_eq_true.mp obligations item selected)

/-- Synchronous raw rounds start with no known key. -/
def rounds (table : Table) (fuel : Nat) : Int → Bool :=
  Productivity.iterate (rawStep table) (fun _ => false) fuel

/-- Every raw round is exactly the corresponding finite-carrier iterate. -/
theorem restrict_rounds (table : Table) (fuel : Nat) :
    restrict table (rounds table fuel) =
      Productivity.iterate (ConservativeEmptiness.step (rows table)) (fun _ => false) fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      change restrict table (rawStep table (rounds table fuel)) =
        ConservativeEmptiness.step (rows table)
          (Productivity.iterate (ConservativeEmptiness.step (rows table)) (fun _ => false) fuel)
      rw [restrict_step, ih]

/-- No synchronous round marks a key missing from the actual table. -/
theorem rounds_absent (table : Table) (fuel : Nat) (key : Int) (absent : lookup key table = none) :
    rounds table fuel key = false := by
  cases fuel <;> simp [rounds, Productivity.iterate, rawStep, absent]

/-- Raw rounds ascend without a finiteness premise on all integers. -/
theorem rounds_ascending (table : Table) (fuel : Nat) :
    Productivity.Included (rounds table fuel) (rounds table (fuel + 1)) :=
  Productivity.iterate_ascending _ _ (rawStep_monotone table) (by intro key impossible; cases impossible) fuel

/-- Run one synchronous round per stored entry. -/
def possible (table : Table) : Int → Bool := rounds table table.length

/-- The table-computed result agrees with the existing finite fixed-point algorithm. -/
theorem possible_agrees (table : Table) :
    restrict table (possible table) = ConservativeEmptiness.possible (states table) (rows table) := by
  simpa only [possible, ConservativeEmptiness.possible, states_length] using restrict_rounds table table.length

/-- The raw public query negates the table's computed possibility result. -/
def provablyEmpty (table : Table) (query : Item) : Bool := !rawCanAccept table (possible table) query

/-- The raw public query is exactly the finite-carrier algorithm on the actual classifier. -/
theorem provablyEmpty_agrees (table : Table) (query : Item) :
    provablyEmpty table query =
      ConservativeEmptiness.provablyEmpty (states table) (rows table) (classify table query) := by
  rw [provablyEmpty, canAccept_agrees, possible_agrees]
  rfl

/-- Actual finite table keys suffice to prove a fixed point of the full raw operator. -/
theorem possible_fixed (table : Table) : rawStep table (possible table) = possible table := by
  funext key
  by_cases present : key ∈ table.map Prod.fst
  · let state : Key table := ⟨key, present⟩
    have fixed := ConservativeEmptiness.possible_fixed (states table) (states_complete table) (rows table)
    calc
      rawStep table (possible table) key =
          ConservativeEmptiness.step (rows table) (restrict table (possible table)) state := step_agrees table _ state
      _ = ConservativeEmptiness.step (rows table)
          (ConservativeEmptiness.possible (states table) (rows table)) state := by rw [possible_agrees]
      _ = ConservativeEmptiness.possible (states table) (rows table) state := congrFun fixed state
      _ = possible table key := (congrFun (possible_agrees table) state).symm
  · have absent := (lookup_none_iff key table).mpr present
    rw [show rawStep table (possible table) key = false by simp [rawStep, absent]]
    exact (rounds_absent table table.length key absent).symm

/-- Any extra rounds retain the exact raw result, including all absent keys. -/
theorem rounds_stable (table : Table) (extra : Nat) : rounds table (table.length + extra) = possible table := by
  induction extra with
  | zero => rfl
  | succ extra ih =>
      change rawStep table (rounds table (table.length + extra)) = possible table
      rw [ih, possible_fixed]

/-- The table result is the least raw state set closed under the actual row operator. -/
theorem possible_least (table : Table) (known : Int → Bool)
    (closed : Productivity.Included (rawStep table known) known) : Productivity.Included (possible table) known :=
  Productivity.iterate_below_closed _ _ known (rawStep_monotone table)
    (by intro key impossible; cases impossible) closed table.length

/-- Compare known sets only at stored keys, as finite map-key equality does. -/
def same (table : Table) (left right : Int → Bool) : Bool :=
  (table.map Prod.fst).all (fun key => left key == right key)

/-- Finite equality is reflexive even when a table contains repeated keys. -/
theorem same_refl (table : Table) (known : Int → Bool) : same table known known = true := by simp [same]

/-- Finite equality determines the full set when both sets omit every absent key. -/
theorem same_eq (table : Table) (left right : Int → Bool)
    (leftAbsent : ∀ key, lookup key table = none → left key = false)
    (rightAbsent : ∀ key, lookup key table = none → right key = false)
    (equal : same table left right = true) : left = right := by
  funext key
  by_cases present : key ∈ table.map Prod.fst
  · exact beq_iff_eq.mp (List.all_eq_true.mp equal key present)
  · have absent := (lookup_none_iff key table).mpr present
    rw [leftAbsent key absent, rightAbsent key absent]

/-- The equality-stop loop retains the current set when the next set is equal. -/
def grow (table : Table) : Nat → (Int → Bool) → Option (Int → Bool)
  | 0, _ => none
  | fuel + 1, known =>
      let next := rawStep table known
      if same table next known then some known else grow table fuel next

/-- Every fixed synchronous round is the least fixed point reached by this table. -/
theorem fixed_round_eq (table : Table) (fuel : Nat)
    (fixed : rawStep table (rounds table fuel) = rounds table fuel) : rounds table fuel = possible table := by
  have lower := possible_least table (rounds table fuel) (fun key marked => by rwa [fixed] at marked)
  have upper : Productivity.Included (rounds table fuel) (possible table) :=
    Productivity.iterate_below_closed _ _ (possible table) (rawStep_monotone table)
      (by intro key impossible; cases impossible) (fun key marked => by rwa [possible_fixed] at marked) fuel
  funext key
  have first := lower key
  have second := upper key
  cases a : rounds table fuel key <;> cases b : possible table key <;> simp_all

/-- Every actual completed equality-stop result from a synchronous round is the same least fixed point. -/
theorem grow_rounds_result (table : Table) (fuel start : Nat) (result : Int → Bool)
    (done : grow table fuel (rounds table start) = some result) : result = possible table := by
  induction fuel generalizing start with
  | zero => simp [grow] at done
  | succ fuel ih =>
      rw [grow] at done
      by_cases stopped : same table (rawStep table (rounds table start)) (rounds table start) = true
      · have fixed := same_eq table _ _ (fun key absent => by simp [rawStep, absent])
          (rounds_absent table start) stopped
        simp only [stopped, ↓reduceIte, Option.some.injEq] at done
        exact done.symm.trans (fixed_round_eq table start fixed)
      · simp only [stopped] at done
        exact ih (start + 1) done

/-- The equality-stop loop completes once enough remaining rounds cover the table length. -/
theorem grow_rounds_complete (table : Table) (fuel start : Nat) (enough : table.length ≤ start + fuel) :
    grow table (fuel + 1) (rounds table start) = some (possible table) := by
  induction fuel generalizing start with
  | zero =>
      have later : start = table.length + (start - table.length) := by omega
      have stable : rounds table start = possible table := by rw [later]; exact rounds_stable table _
      simp only [grow, stable, possible_fixed, same_refl, ↓reduceIte]
  | succ fuel ih =>
      rw [grow]
      by_cases stopped : same table (rawStep table (rounds table start)) (rounds table start) = true
      · have fixed := same_eq table _ _ (fun key absent => by simp [rawStep, absent])
          (rounds_absent table start) stopped
        simp only [stopped]
        exact congrArg some (fixed_round_eq table start fixed)
      · simp only [stopped]
        exact ih (start + 1) (by omega)

/-- A table supplies a finite bound for its actual equality-stop computation from the empty known set. -/
theorem grow_complete (table : Table) : grow table (table.length + 1) (fun _ => false) = some (possible table) :=
  grow_rounds_complete table table.length 0 (by omega)

end MicroCFTA.ConservativeEmptinessTable
