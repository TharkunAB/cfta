import MicroCFTA.SourceSizedDecidedFilter

/-!
# The finite table folds in `Data.CFTA.Sized.sizedUpTo`

Each size pass reads one frozen table. Inserts for other states at the
current size do not affect its candidates. Tables use extensional lookup;
the source Map representation must implement these lookup and insert laws.
-/

namespace MicroCFTA.SourceSizedDecidedTable

/-- Missing table entries return the empty class. -/
abbrev Table (State Value : Type) := State → Nat → List Value

/-- Insert one complete class without changing any other table entry. -/
def insert [DecidableEq State] (table : Table State Value) (state : State)
    (size : Nat) (terms : List Value) : Table State Value :=
  fun query count => if query = state ∧ count = size then terms else table query count

/-- Decide one state after the preceding states, retaining the frozen input. -/
def addStates [DecidableEq State]
    (make : Table State Value → Nat → State → Except Error (List Value))
    (smaller : Table State Value) (size : Nat) :
    List State → Table State Value → Except Error (Table State Value)
  | [], built => .ok built
  | state :: rest, built =>
      match make smaller size state with
      | .error error => .error error
      | .ok terms => addStates make smaller size rest (insert built state size terms)

/-- Build sizes one through the bound, including every empty size class. -/
def upTo [DecidableEq State]
    (make : Table State Value → Nat → State → Except Error (List Value))
    (states : List State) : Nat → Except Error (Table State Value)
  | 0 => .ok (fun _ _ => [])
  | bound + 1 =>
      match upTo make states bound with
      | .error error => .error error
      | .ok smaller => addStates make smaller (bound + 1) states smaller

/-- The state recursion is the source monadic left fold with frozen smaller classes. -/
theorem addStates_eq_foldlM [DecidableEq State]
    (make : Table State Value → Nat → State → Except Error (List Value))
    (smaller : Table State Value) (size : Nat) (states : List State) (built : Table State Value) :
    addStates make smaller size states built = states.foldlM
      (fun table state => (make smaller size state).map (insert table state size)) built := by
  induction states generalizing built with
  | nil => rfl
  | cons state rest ih =>
      rw [List.foldlM_cons]
      cases result : make smaller size state with
      | error error => simp [addStates, result, Except.map, bind, Except.bind]
      | ok terms => simpa [addStates, result, Except.map, bind, Except.bind] using ih (insert built state size terms)

/-- The size recursion is the ascending source fold over sizes one through the bound. -/
theorem upTo_eq_foldlM [DecidableEq State]
    (make : Table State Value → Nat → State → Except Error (List Value))
    (states : List State) (bound : Nat) :
    upTo make states bound = (List.range bound).foldlM
      (fun smaller previous => addStates make smaller (previous + 1) states smaller) (fun _ _ => []) := by
  induction bound with
  | zero => rfl
  | succ bound ih =>
      rw [List.range_succ, List.foldlM_append, ← ih]
      cases previous : upTo make states bound with
      | error error => simp [upTo, previous, bind, Except.bind]
      | ok smaller =>
          simp [upTo, previous, List.foldlM_cons, List.foldlM_nil, bind, Except.bind]
          cases addStates make smaller (bound + 1) states smaller <;> rfl

/-- A state pass succeeds if every class call succeeds. -/
theorem addStates_success [DecidableEq State]
    (make : Table State Value → Nat → State → Except Error (List Value))
    (completed : ∀ smaller size state, ∃ terms, make smaller size state = .ok terms)
    (smaller : Table State Value) (size : Nat) (states : List State) (built : Table State Value) :
    ∃ output, addStates make smaller size states built = .ok output := by
  induction states generalizing built with
  | nil => exact ⟨built, rfl⟩
  | cons state rest ih =>
      obtain ⟨terms, done⟩ := completed smaller size state
      obtain ⟨output, tail⟩ := ih (insert built state size terms)
      exact ⟨output, by simpa [addStates, done] using tail⟩

/-- The bounded table succeeds if every class call succeeds. -/
theorem upTo_success [DecidableEq State]
    (make : Table State Value → Nat → State → Except Error (List Value))
    (completed : ∀ smaller size state, ∃ terms, make smaller size state = .ok terms)
    (states : List State) (bound : Nat) : ∃ output, upTo make states bound = .ok output := by
  induction bound with
  | zero => exact ⟨_, rfl⟩
  | succ bound ih =>
      obtain ⟨smaller, previous⟩ := ih
      obtain ⟨output, next⟩ := addStates_success make completed smaller (bound + 1) states smaller
      exact ⟨output, by simpa [upTo, previous] using next⟩

/-- A successful state fold changes exactly the listed states at this size. -/
theorem addStates_exact [DecidableEq State]
    (make : Table State Value → Nat → State → Except Error (List Value))
    (smaller : Table State Value) (size : Nat) (states : List State)
    (expected : State → List Value)
    (correct : ∀ state ∈ states, ∀ terms,
      make smaller size state = .ok terms → terms = expected state)
    (built output : Table State Value)
    (success : addStates make smaller size states built = .ok output) :
    ∀ state count, output state count =
      if state ∈ states ∧ count = size then expected state else built state count := by
  induction states generalizing built with
  | nil =>
      have equal : built = output := by simpa [addStates] using success
      subst output
      simp
  | cons first rest ih =>
      cases result : make smaller size first with
      | error error => simp [addStates, result] at success
      | ok terms =>
          have same := correct first (by simp) terms result
          have next : addStates make smaller size rest (insert built first size terms) = .ok output := by
            simpa [addStates, result] using success
          have tail := ih (fun state present => correct state (by simp [present]))
            (insert built first size terms) next
          intro state count
          rw [tail]
          by_cases inRest : state ∈ rest
          · by_cases sameSize : count = size <;> simp [inRest, sameSize, insert]
          · by_cases sameState : state = first
            · subst state
              simp [inRest, insert, same]
            · simp [inRest, sameState, insert]

/-- A failed state fold stops at the first failing class in the state order. -/
theorem addStates_error_iff [DecidableEq State]
    (make : Table State Value → Nat → State → Except Error (List Value))
    (smaller : Table State Value) (size : Nat) (states : List State)
    (built : Table State Value) (error : Error) :
    addStates make smaller size states built = .error error ↔
      ∃ before state after intermediate,
        states = before ++ state :: after ∧
        addStates make smaller size before built = .ok intermediate ∧
        make smaller size state = .error error := by
  induction states generalizing built with
  | nil => simp [addStates]
  | cons first rest ih =>
      cases result : make smaller size first with
      | error bad =>
          constructor
          · intro failed
            have same : bad = error := by simpa [addStates, result] using failed
            subst error
            exact ⟨[], first, rest, built, rfl, rfl, result⟩
          · rintro ⟨before, state, after, intermediate, same, priorClasses, failed⟩
            cases before with
            | nil =>
                have equal : first = state := by simpa using congrArg List.head? same
                subst state
                simpa [addStates, result] using failed
            | cons initial tail =>
                have equal : first = initial := by simpa using congrArg List.head? same
                subst initial
                simp [addStates, result] at priorClasses
      | ok terms =>
          simp only [addStates, result]
          rw [ih]
          constructor
          · rintro ⟨before, state, after, intermediate, same, priorClasses, failed⟩
            exact ⟨first :: before, state, after, intermediate,
              by simp [same], by simpa [addStates, result] using priorClasses, failed⟩
          · rintro ⟨before, state, after, intermediate, same, priorClasses, failed⟩
            cases before with
            | nil =>
                have equal : first = state := by simpa using congrArg List.head? same
                subst state
                simp [result] at failed
            | cons initial tail =>
                have equal : first = initial := by simpa using congrArg List.head? same
                have restEqual : rest = tail ++ state :: after := by
                  simpa using congrArg List.tail same
                subst initial
                exact ⟨tail, state, after, intermediate, restEqual,
                  by simpa [addStates, result] using priorClasses, failed⟩

/-- A failed size fold stops after a successful prefix of complete sizes. -/
theorem upTo_error_iff [DecidableEq State]
    (make : Table State Value → Nat → State → Except Error (List Value))
    (states : List State) (bound : Nat) (error : Error) :
    upTo make states bound = .error error ↔
      ∃ earlier smaller, earlier < bound ∧ upTo make states earlier = .ok smaller ∧
        addStates make smaller (earlier + 1) states smaller = .error error := by
  induction bound with
  | zero => simp [upTo]
  | succ bound ih =>
      cases previous : upTo make states bound with
      | error bad =>
          constructor
          · intro failed
            have equal : bad = error := by simpa [upTo, previous] using failed
            subst error
            obtain ⟨earlier, smaller, within, done, failed⟩ := ih.mp previous
            exact ⟨earlier, smaller, by omega, done, failed⟩
          · rintro ⟨earlier, smaller, within, done, failed⟩
            have lt : earlier < bound := by
              by_cases strict : earlier < bound
              · exact strict
              · have same : earlier = bound := by omega
                subst earlier
                rw [previous] at done
                cases done
            have prior := ih.mpr ⟨earlier, smaller, lt, done, failed⟩
            simp [upTo, prior]
      | ok smaller =>
          constructor
          · intro failed
            exact ⟨bound, smaller, by omega, previous, by simpa [upTo, previous] using failed⟩
          · rintro ⟨earlier, table, within, done, failed⟩
            by_cases equal : earlier = bound
            · subst earlier
              have same : table = smaller := by rw [previous] at done; exact Except.ok.inj done.symm
              subst table
              simpa [upTo, previous] using failed
            · have prior := ih.mpr ⟨earlier, table, by omega, done, failed⟩
              rw [previous] at prior
              cases prior

/-- The entire table agrees with the reference inside its state and size domain. -/
def Matches (states : List State) [DecidableEq State]
    (reference : Nat → State → List Value) (bound : Nat) (table : Table State Value) : Prop :=
  ∀ state size, table state size =
    if state ∈ states ∧ 0 < size ∧ size ≤ bound then reference size state else []

/-- Successful finite table construction has exactly the reference classes. -/
theorem upTo_exact [DecidableEq State]
    (make : Table State Value → Nat → State → Except Error (List Value))
    (states : List State) (reference : Nat → State → List Value)
    (correct : ∀ bound smaller, Matches states reference bound smaller →
      ∀ state ∈ states, ∀ terms,
        make smaller (bound + 1) state = .ok terms → terms = reference (bound + 1) state)
    (bound : Nat) (output : Table State Value)
    (success : upTo make states bound = .ok output) : Matches states reference bound output := by
  induction bound generalizing output with
  | zero =>
      have same : (fun _ _ => []) = output := by simpa [upTo] using success
      subst output
      intro state size
      simp only
      split <;> rename_i condition
      · omega
      · rfl
  | succ bound ih =>
      cases previous : upTo make states bound with
      | error error => simp [upTo, previous] at success
      | ok smaller =>
          have matched := ih smaller previous
          have next : addStates make smaller (bound + 1) states smaller = .ok output := by
            simpa [upTo, previous] using success
          have exactStates := addStates_exact make smaller (bound + 1) states
            (reference (bound + 1)) (correct bound smaller matched) smaller output next
          intro state size
          rw [exactStates, matched]
          by_cases present : state ∈ states
          · by_cases atSize : size = bound + 1
            · subst size
              simp [present]
            · have bounds : size ≤ bound + 1 ↔ size ≤ bound := by omega
              simp [present, atSize, bounds]
          · simp [present]

/-- Successful construction leaves every class above its bound empty. -/
theorem upTo_above [DecidableEq State]
    (make : Table State Value → Nat → State → Except Error (List Value))
    (states : List State) (bound : Nat) (output : Table State Value)
    (success : upTo make states bound = .ok output) :
    ∀ state size, bound < size → output state size = [] := by
  induction bound generalizing output with
  | zero =>
      have same : (fun _ _ => []) = output := by simpa [upTo] using success
      subst output
      simp
  | succ bound ih =>
      cases previous : upTo make states bound with
      | error error => simp [upTo, previous] at success
      | ok smaller =>
          have above := ih smaller previous
          have next : addStates make smaller (bound + 1) states smaller = .ok output := by
            simpa [upTo, previous] using success
          have frame : ∀ (todo : List State) (built output : Table State Value),
              addStates make smaller (bound + 1) todo built = .ok output →
              ∀ state size, size ≠ bound + 1 → output state size = built state size := by
            intro todo
            induction todo with
            | nil =>
                intro built output same
                have equal : built = output := by simpa [addStates] using same
                subst output
                simp
            | cons first rest tail =>
                intro built output success state size different
                cases result : make smaller (bound + 1) first with
                | error error => simp [addStates, result] at success
                | ok terms =>
                    have remaining : addStates make smaller (bound + 1) rest
                        (insert built first (bound + 1) terms) = .ok output := by
                      simpa [addStates, result] using success
                    rw [tail _ _ remaining state size different]
                    simp [insert, different]
          intro state size larger
          rw [frame states smaller output next state size (by omega)]
          exact above state size (by omega)

end MicroCFTA.SourceSizedDecidedTable
