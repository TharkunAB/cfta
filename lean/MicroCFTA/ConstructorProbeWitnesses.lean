import MicroCFTA.Generic
import MicroCFTA.Productivity
import MicroCFTA.Cache

/-!
# Actual constructor-probe witness discovery

The source keeps the first usable transition of each state. Each pass folds
the ordered finite table from right to left. The loop stops when the number
of witnessed states does not change.
-/
namespace MicroCFTA.ConstructorProbeWitnesses
open Language Cache
variable {State Symbol : Type}

/-- A graph row retains constructor labels and ordered child states. -/
abbrev Rows (State Symbol : Type) := State → Generic.Row State Symbol

/-- One admitted structural term, with no annotation predicate. -/
abbrev Admits (rows : Rows State Symbol) := Accepts (fun state => Generic.edges (rows state))

/-- The source map holds one complete term per discovered productive state. -/
abbrev Witnesses (State Symbol : Type) := State → Option (Term Symbol)

/-- Traverse all child lookups in their original order. -/
def arguments (known : Witnesses State Symbol) : List State → Option (List (Term Symbol))
  | [] => some []
  | first :: rest => do
      let head ← known first
      let tail ← arguments known rest
      pure (head :: tail)

/-- Child traversal succeeds exactly when each position has its recorded witness. -/
theorem arguments_exact (known : Witnesses State Symbol) (children : List State) (terms : List (Term Symbol)) :
    arguments known children = some terms ↔ All₂ (fun state term => known state = some term) children terms := by
  induction children generalizing terms with
  | nil =>
      constructor
      · intro found
        have same : terms = [] := Option.some.inj found.symm
        subst terms
        exact .nil
      · intro related
        cases related
        rfl
  | cons child children ih =>
      cases head : known child with
      | none =>
          constructor
          · simp [arguments, head]
          · intro related
            cases related with
            | cons first rest => simp [head] at first
      | some term =>
          cases tail : arguments known children with
          | none =>
              constructor
              · simp [arguments, head, tail]
              · intro related
                cases related with
                | cons first rest => have := (ih _).mpr rest; simp [tail] at this
          | some values =>
              have rest := (ih _).mp tail
              constructor
              · intro result
                have same : terms = term :: values := by simpa [arguments, head, tail] using result.symm
                subst terms
                exact .cons head rest
              · intro related
                cases related with
                | cons first rest =>
                    have same := Option.some.inj (head.symm.trans first)
                    have equal := Option.some.inj (tail.symm.trans ((ih _).mpr rest))
                    subst_vars
                    simp [arguments, head, tail]

/-- Previously selected child witnesses survive every extension of the map. -/
theorem arguments_grows (before after : Witnesses State Symbol) (growth : Extends before after)
    (children : List State) (terms : List (Term Symbol)) (found : arguments before children = some terms) :
    arguments after children = some terms := by
  apply (arguments_exact _ _ _).mpr
  have related := (arguments_exact _ _ _).mp found
  clear found
  induction related with
  | nil => exact .nil
  | cons first rest ih => exact .cons (growth _ _ first) ih

/-- Keep the first transition whose ordered child witnesses all exist. -/
def firstWitness (known : Witnesses State Symbol) : Generic.Row State Symbol → Option (Term Symbol)
  | [] => none
  | (symbol, children) :: rest =>
      match arguments known children with
      | some terms => some (.node symbol terms)
      | none => firstWitness known rest

/-- A selected witness is the exact term of one listed transition. -/
theorem firstWitness_exact (known : Witnesses State Symbol) (row : Generic.Row State Symbol)
    (term : Term Symbol) (found : firstWitness known row = some term) :
    ∃ symbol children terms, (symbol, children) ∈ row ∧ arguments known children = some terms ∧ term = .node symbol terms := by
  induction row with
  | nil => simp [firstWitness] at found
  | cons edge rest ih =>
      rcases edge with ⟨symbol, children⟩
      cases ready : arguments known children with
      | none =>
          obtain ⟨label, states, terms, member, args, same⟩ := ih (by simpa [firstWitness, ready] using found)
          exact ⟨label, states, terms, List.mem_cons_of_mem _ member, args, same⟩
      | some terms =>
          exact ⟨symbol, children, terms, by simp, ready, by simpa [firstWitness, ready] using found.symm⟩

/-- At least one usable transition makes the first-witness search succeed. -/
theorem firstWitness_available (known : Witnesses State Symbol) (row : Generic.Row State Symbol)
    (symbol : Symbol) (children : List State) (terms : List (Term Symbol))
    (member : (symbol, children) ∈ row) (ready : arguments known children = some terms) :
    ∃ term, firstWitness known row = some term := by
  induction row with
  | nil => simp at member
  | cons edge rest ih =>
      rcases edge with ⟨label, states⟩
      cases found : arguments known states with
      | some values => exact ⟨.node label values, by simp [firstWitness, found]⟩
      | none =>
          have later : (symbol, children) ∈ rest := by
            rcases List.mem_cons.mp member with same | later
            · cases same; simp [found] at ready
            · exact later
          simpa [firstWitness, found] using ih later

/-- Add a witness only when the state has no earlier record. -/
def addWitness [DecidableEq State] (rows : Rows State Symbol) (state : State)
    (known : Witnesses State Symbol) : Witnesses State Symbol :=
  match known state with
  | some _ => known
  | none =>
      match firstWitness known (rows state) with
      | none => known
      | some term => put known state term

/-- Witness discovery never replaces an existing term. -/
theorem addWitness_grows [DecidableEq State] (rows : Rows State Symbol) (state : State)
    (known : Witnesses State Symbol) : Extends known (addWitness rows state known) := by
  intro other term stored
  cases found : known state with
  | some value => simpa [addWitness, found] using stored
  | none =>
      cases candidate : firstWitness known (rows state) with
      | none => simpa [addWitness, found, candidate] using stored
      | some value =>
          have different : other ≠ state := by intro same; subst other; simp [found] at stored
          simpa [addWitness, found, candidate, put, different] using stored

/-- A usable transition always leaves its owner witnessed after the source update. -/
theorem addWitness_fills [DecidableEq State] (rows : Rows State Symbol) (state : State)
    (known : Witnesses State Symbol) (symbol : Symbol) (children : List State) (terms : List (Term Symbol))
    (member : (symbol, children) ∈ rows state) (ready : arguments known children = some terms) :
    ∃ term, addWitness rows state known state = some term := by
  cases found : known state with
  | some term => exact ⟨term, by simp [addWitness, found]⟩
  | none =>
      obtain ⟨term, selected⟩ := firstWitness_available known (rows state) symbol children terms member ready
      exact ⟨term, by simp [addWitness, found, selected, put]⟩

/-- Every stored witness is admitted by its actual graph state. -/
def Sound (rows : Rows State Symbol) (known : Witnesses State Symbol) : Prop :=
  ∀ state term, known state = some term → Admits rows state term

/-- Source witness insertion preserves admission of every recorded term. -/
theorem addWitness_sound [DecidableEq State] (rows : Rows State Symbol) (state : State)
    (known : Witnesses State Symbol) (sound : Sound rows known) : Sound rows (addWitness rows state known) := by
  intro other term stored
  cases found : known state with
  | some value => exact sound _ _ (by simpa [addWitness, found] using stored)
  | none =>
      cases candidate : firstWitness known (rows state) with
      | none => exact sound _ _ (by simpa [addWitness, found, candidate] using stored)
      | some value =>
          by_cases same : other = state
          · subst other
            have valueEq : value = term := by simpa [addWitness, found, candidate, put] using stored
            subst term
            obtain ⟨symbol, children, terms, member, ready, shape⟩ := firstWitness_exact known (rows state) value candidate
            subst value
            have related := (arguments_exact _ _ _).mp ready
            have accepted : All₂ (Admits rows) children terms := by
              clear stored candidate ready member found
              induction related with
              | nil => exact .nil
              | cons first rest ih => exact .cons (sound _ _ first) ih
            exact .node ⟨symbol, children, fun _ => true⟩ terms
              (List.mem_map.mpr ⟨(symbol, children), member, rfl⟩) accepted rfl
          · exact sound _ _ (by simpa [addWitness, found, candidate, put, same] using stored)

/-- Fold the source table in its ascending-map right-fold order. -/
def passRows [DecidableEq State] (order : List State) (rows : Rows State Symbol) (known : Witnesses State Symbol) :
    Witnesses State Symbol := order.foldr (addWitness rows) known

/-- A complete pass retains every earlier witness. -/
theorem passRows_grows [DecidableEq State] (order : List State) (rows : Rows State Symbol)
    (known : Witnesses State Symbol) : Extends known (passRows order rows known) := by
  induction order with
  | nil => exact extends_refl _
  | cons state rest ih => exact extends_trans ih (addWitness_grows rows state _)

/-- A complete pass preserves witness admission. -/
theorem passRows_sound [DecidableEq State] (order : List State) (rows : Rows State Symbol)
    (known : Witnesses State Symbol) (sound : Sound rows known) : Sound rows (passRows order rows known) := by
  induction order with
  | nil => exact sound
  | cons state rest ih => exact addWitness_sound rows state _ ih

/-- Every transition usable at pass entry leaves its owner witnessed by pass exit. -/
theorem passRows_fills [DecidableEq State] (order : List State) (rows : Rows State Symbol)
    (known : Witnesses State Symbol) (state : State) (symbol : Symbol) (children : List State) (terms : List (Term Symbol))
    (listed : state ∈ order) (member : (symbol, children) ∈ rows state) (ready : arguments known children = some terms) :
    ∃ term, passRows order rows known state = some term := by
  induction order with
  | nil => simp at listed
  | cons first rest ih =>
      rcases List.mem_cons.mp listed with same | later
      · subst first
        exact addWitness_fills rows state _ symbol children terms member
          (arguments_grows known _ (passRows_grows rest rows known) children terms ready)
      · obtain ⟨term, stored⟩ := ih later
        exact ⟨term, addWitness_grows rows first _ _ _ stored⟩

/-- Count the source map's occupied keys in the finite state inventory. -/
def occupied (known : Witnesses (Fin count) Symbol) : Nat :=
  (List.finRange count).countP fun state => (known state).isSome

/-- Map extension cannot reduce its source size. -/
theorem occupied_mono (before after : Witnesses (Fin count) Symbol) (growth : Extends before after) :
    occupied before ≤ occupied after := by
  apply List.countP_mono_left
  intro state _ present
  obtain ⟨term, stored⟩ := Option.isSome_iff_exists.mp present
  exact Option.isSome_iff_exists.mpr ⟨term, growth _ _ stored⟩

/-- The map can contain at most one witness for each listed finite state. -/
theorem occupied_bound (known : Witnesses (Fin count) Symbol) : occupied known ≤ count := by
  simpa [occupied] using List.countP_le_length (p := fun state => (known state).isSome) (l := List.finRange count)

/-- Equal source map sizes after an extension imply equality of all retained witness terms. -/
theorem equal_size (before after : Witnesses (Fin count) Symbol) (growth : Extends before after)
    (sameSize : occupied after = occupied before) : after = before := by
  funext state
  cases old : before state with
  | some term => exact growth state term old
  | none =>
      cases fresh : after state with
      | none => rfl
      | some term =>
          have strict : occupied before < occupied after := by
            apply Productivity.count_strict
            · intro other _ present
              obtain ⟨value, stored⟩ := Option.isSome_iff_exists.mp present
              exact Option.isSome_iff_exists.mpr ⟨value, growth _ _ stored⟩
            · exact ⟨state, List.mem_finRange state, by simp [old], by simp [fresh]⟩
          omega

/-- One pass over the exact finite row inventory. -/
def pass (rows : Rows (Fin count) Symbol) (known : Witnesses (Fin count) Symbol) : Witnesses (Fin count) Symbol :=
  passRows (List.finRange count) rows known

/-- Follow the source's unchanged-size test until no new productive state appears. -/
def converge (rows : Rows (Fin count) Symbol) (known : Witnesses (Fin count) Symbol) : Witnesses (Fin count) Symbol :=
  let next := pass rows known
  if _same : occupied next = occupied known then known else converge rows next
termination_by count - occupied known
decreasing_by
  have grows := occupied_mono known (pass rows known) (passRows_grows _ _ _)
  have bound := occupied_bound (pass rows known)
  have different : occupied (pass rows known) ≠ occupied known := _same
  omega

/-- Actual convergence terminates with a sound fixed point and preserves every earlier witness. -/
theorem converge_correct (rows : Rows (Fin count) Symbol) (known : Witnesses (Fin count) Symbol)
    (sound : Sound rows known) :
    Sound rows (converge rows known) ∧ pass rows (converge rows known) = converge rows known ∧
      Extends known (converge rows known) := by
  induction known using converge.induct rows with
  | case1 known next same =>
      change occupied (pass rows known) = occupied known at same
      rw [converge]
      simp only [same, dite_true]
      exact ⟨sound, equal_size known _ (passRows_grows _ _ _) same, extends_refl _⟩
  | case2 known next different ih =>
      change occupied (pass rows known) ≠ occupied known at different
      rw [converge]
      simp only [different, dite_false]
      have later := ih (passRows_sound _ _ _ sound)
      exact ⟨later.1, later.2.1, extends_trans (passRows_grows _ _ _) later.2.2⟩

/-- At the computed fixed point, every finite accepting run has a stored witness. -/
theorem fixed_complete (rows : Rows (Fin count) Symbol) (known : Witnesses (Fin count) Symbol)
    (fixed : pass rows known = known) {state : Fin count} {term : Term Symbol} (accepted : Admits rows state term) :
    ∃ value, known state = some value := by
  induction accepted using Accepts.rec
    (motive_2 := fun states _ _ => ∃ terms, arguments known states = some terms) with
  | @node state edge terms member runs guard ih =>
      obtain ⟨row, listed, same⟩ := List.mem_map.mp member
      rcases row with ⟨symbol, children⟩
      subst edge
      obtain ⟨witnesses, ready⟩ := ih
      have found := passRows_fills (List.finRange count) rows known state symbol children witnesses
        (List.mem_finRange state) listed ready
      change ∃ value, pass rows known state = some value at found
      rw [fixed] at found
      exact found
  | nil => exact ⟨[], rfl⟩
  | cons first rest ih ihs =>
      obtain ⟨head, headFound⟩ := ih
      obtain ⟨tail, tailFound⟩ := ihs
      exact ⟨head :: tail, by simp [arguments, headFound, tailFound]⟩

/-- Run the exact source witness search from the empty map. -/
def witnesses (rows : Rows (Fin count) Symbol) : Witnesses (Fin count) Symbol := converge rows (fun _ => none)

/-- Every actual selected term is admitted by its graph state. -/
theorem witnesses_sound (rows : Rows (Fin count) Symbol) : Sound rows (witnesses rows) :=
  (converge_correct rows (fun _ => none) (by intro state term impossible; cases impossible)).1

/-- The actual witness map contains exactly the productive states of the finite graph. -/
theorem witnesses_exact (rows : Rows (Fin count) Symbol) (state : Fin count) :
    (∃ value, witnesses rows state = some value) ↔ ∃ term, Admits rows state term := by
  constructor
  · rintro ⟨value, stored⟩
    exact ⟨value, witnesses_sound rows state value stored⟩
  · rintro ⟨term, accepted⟩
    exact fixed_complete rows (witnesses rows)
      (converge_correct rows (fun _ => none) (by intro state term impossible; cases impossible)).2.1 accepted

end MicroCFTA.ConstructorProbeWitnesses
