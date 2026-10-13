import MicroCFTA.SourceSizedLiquidPublic

/-!
# Whole bounded liquid execution with exceptions

The candidate filter preserves returned GuardUnknown and raised solver
exceptions as separate stops. The existing ordered state and size folds
propagate either stop. Each external query occurrence has its own reply.
-/

namespace MicroCFTA.SourceSizedLiquidExecution

open Language Guards SourceSizedDecidedTable SourceSizedDecidedExecution
open SourceSizedDecided SourceSizedLiquidProgram SolverAdapter

/-- A returned GuardUnknown and an IO exception have different constructors. -/
inductive Halt (Item : Type) where
  | unknown (item : Item)
  | raised (failure : SolverAdapter.Failure)

/-- The outside error is an IO exception; the inside error is GuardUnknown. -/
abbrev Outcome (Item Value : Type) := Except SolverAdapter.Failure (Except Item Value)

/-- Encode the two source failure channels for the common ordered folds. -/
def encode : Outcome Item Value → Except (Halt Item) Value
  | .error failure => .error (.raised failure)
  | .ok (.error item) => .error (.unknown item)
  | .ok (.ok value) => .ok value

/-- Decode a fold stop without converting exceptions into Unknown. -/
def decode : Except (Halt Item) Value → Outcome Item Value
  | .error (.raised failure) => .error failure
  | .error (.unknown item) => .ok (.error item)
  | .ok value => .ok (.ok value)

theorem encode_decode (result : Except (Halt Item) Value) : encode (decode result) = result := by
  cases result with
  | ok value => rfl
  | error failure => cases failure <;> rfl

/-- Candidate evaluation stops immediately at Unknown or a raised exception. -/
inductive FilterRun (evaluates : Item → Nat → SolverAdapter.Result → Prop) :
    List Item → Except (Halt Item) (List Item) → Nat → Prop where
  | nil : FilterRun evaluates [] (.ok []) 0
  | unknown : evaluates item work (.returned .unknown) →
      FilterRun evaluates (item :: rest) (.error (.unknown item)) (work + 1)
  | raised {failure : SolverAdapter.Failure} : evaluates item work (.raised failure) →
      FilterRun evaluates (item :: rest) (.error (.raised failure)) (work + 1)
  | no : evaluates item work (.returned .no) → FilterRun evaluates rest result tailWork →
      FilterRun evaluates (item :: rest) result (work + tailWork + 1)
  | yesOk : evaluates item work (.returned .yes) → FilterRun evaluates rest (.ok kept) tailWork →
      FilterRun evaluates (item :: rest) (.ok (item :: kept)) (work + tailWork + 1)
  | yesError : evaluates item work (.returned .yes) → FilterRun evaluates rest (.error bad) tailWork →
      FilterRun evaluates (item :: rest) (.error bad) (work + tailWork + 1)

/-- Restrict evaluator traces to returned verdicts without imposing stable replies. -/
def returned (evaluates : Item → Nat → SolverAdapter.Result → Prop) : Item → Nat → Verdict → Prop :=
  fun item work verdict => evaluates item work (.returned verdict)

/-- Every successful filter is an existing returned-verdict trace at the same work. -/
theorem filter_success (evaluates : Item → Nat → SolverAdapter.Result → Prop)
    {items result work} (run : FilterRun evaluates items result work) :
    ∀ output, result = .ok output → SourceSizedDecidedFilter.Run (returned evaluates) items (.ok output) work := by
  induction run with
  | nil => intro output same; cases same; exact .nil
  | unknown completed => intro output impossible; cases impossible
  | raised completed => intro output impossible; cases impossible
  | no completed tail ih => intro output same; exact .no completed (ih output same)
  | yesOk completed tail ih => intro output same; cases same; exact .yesOk completed (ih _ rfl)
  | yesError completed tail ih => intro output impossible; cases impossible

/-- A candidate filter has a finite outcome when each evaluation has one. -/
theorem filter_finite (evaluates : Item → Nat → SolverAdapter.Result → Prop)
    (completed : ∀ item, ∃ work result, evaluates item work result) (items : List Item) :
    ∃ result work, FilterRun evaluates items result work := by
  induction items with
  | nil => exact ⟨.ok [], 0, .nil⟩
  | cons item rest ih =>
      obtain ⟨work, result, called⟩ := completed item
      cases result with
      | raised failure => exact ⟨.error (.raised failure), work + 1, .raised called⟩
      | returned verdict =>
          cases verdict with
          | unknown => exact ⟨.error (.unknown item), work + 1, .unknown called⟩
          | no =>
              obtain ⟨result, tailWork, tail⟩ := ih
              exact ⟨result, work + tailWork + 1, .no called tail⟩
          | yes =>
              obtain ⟨result, tailWork, tail⟩ := ih
              cases result with
              | error bad => exact ⟨.error bad, work + tailWork + 1, .yesError called tail⟩
              | ok accepted => exact ⟨.ok (item :: accepted), work + tailWork + 1, .yesOk called tail⟩

/-- A failed evaluation retains its exact Unknown pair or its exact exception. -/
def Caused (evaluates : Item → Nat → SolverAdapter.Result → Prop)
    (bad : Halt Item) (item : Item) (work : Nat) : Prop :=
  match bad with
  | .unknown original => item = original ∧ evaluates item work (.returned .unknown)
  | .raised failure => evaluates item work (.raised failure)

/-- All candidates before the first stop have successful actual evaluations. -/
theorem filter_first_stop (evaluates : Item → Nat → SolverAdapter.Result → Prop)
    {items result work} (run : FilterRun evaluates items result work) :
    ∀ bad, result = .error bad → ∃ before item after accepted beforeWork stopWork,
      items = before ++ item :: after ∧
      SourceSizedDecidedFilter.Run (returned evaluates) before (.ok accepted) beforeWork ∧
      Caused evaluates bad item stopWork := by
  induction run with
  | nil => intro bad impossible; cases impossible
  | @unknown item work rest called =>
      intro bad same
      cases same
      exact ⟨[], item, rest, [], 0, work, rfl, .nil, rfl, called⟩
  | raised called =>
      intro bad same
      cases same
      exact ⟨[], _, _, [], 0, _, rfl, .nil, called⟩
  | @no item work rest result tailWork called tail ih =>
      intro bad same
      obtain ⟨before, failed, after, accepted, beforeWork, stopWork, itemsEq, prior, stopped⟩ := ih bad same
      exact ⟨item :: before, failed, after, accepted, work + beforeWork + 1, stopWork,
        by simp [itemsEq], .no called prior, stopped⟩
  | yesOk called tail ih => intro bad impossible; cases impossible
  | @yesError item work rest bad tailWork called tail ih =>
      intro error same
      obtain ⟨before, failed, after, accepted, beforeWork, stopWork, itemsEq, prior, stopped⟩ := ih error same
      exact ⟨item :: before, failed, after, item :: accepted, work + beforeWork + 1, stopWork,
        by simp [itemsEq], .yesOk called prior, stopped⟩

/-- A complete class filters every candidate before first-occurrence deduplication. -/
inductive ClassRun [DecidableEq Symbol]
    (rows : State → List (Row State Symbol Constraint))
    (evaluates : Constraint × Term Symbol → Nat → SolverAdapter.Result → Prop)
    (smaller : Table State (Term Symbol)) (size : Nat) (state : State) :
    Except (Halt (Constraint × Term Symbol)) (List (Term Symbol)) → Nat → Prop where
  | done : FilterRun evaluates (pairs rows smaller size state) result work →
      ClassRun rows evaluates smaller size state (result.map finish) (work + 1)

/-- Successful classes transfer to the existing public proof without changing their cost. -/
theorem class_success [DecidableEq Symbol] (rows : State → List (Row State Symbol Constraint))
    (evaluates : Constraint × Term Symbol → Nat → SolverAdapter.Result → Prop)
    {smaller size state result work} (run : ClassRun rows evaluates smaller size state result work) :
    ∀ output, result = .ok output →
      SourceSizedDecided.ClassRun rows (returned evaluates) smaller size state (.ok output) work := by
  cases run with
  | @done filtered filterWork finished =>
      intro output same
      cases filtered with
      | error bad => simp [Except.map] at same
      | ok accepted =>
          have equal : finish accepted = output := Except.ok.inj same
          subst output
          exact .done (filter_success evaluates finished accepted rfl)

/-- Each class finishes if every evaluation finishes, even when it raises. -/
theorem class_finite [DecidableEq Symbol] (rows : State → List (Row State Symbol Constraint))
    (evaluates : Constraint × Term Symbol → Nat → SolverAdapter.Result → Prop)
    (completed : ∀ item, ∃ work result, evaluates item work result)
    (smaller : Table State (Term Symbol)) (size : Nat) (state : State) :
    ∃ result work, ClassRun rows evaluates smaller size state result work := by
  obtain ⟨result, work, run⟩ := filter_finite evaluates completed (pairs rows smaller size state)
  exact ⟨result.map finish, work + 1, .done run⟩

/-- Every successful state prefix transfers to the existing returned-verdict trace. -/
theorem states_success [DecidableEq State] [DecidableEq Symbol]
    (rows : State → List (Row State Symbol Constraint))
    (evaluates : Constraint × Term Symbol → Nat → SolverAdapter.Result → Prop)
    {smaller size states built result work}
    (run : StatesRun (ClassRun rows evaluates) smaller size states built result work) :
    ∀ output, result = .ok output →
      StatesRun (SourceSizedDecided.ClassRun rows (returned evaluates)) smaller size states built (.ok output) work := by
  induction run with
  | nil => intro output same; cases same; exact .nil
  | error completed => intro output impossible; cases impossible
  | ok completed tail ih =>
      intro output same
      exact .ok (class_success rows evaluates completed _ rfl) (ih output same)

/-- Every successful size prefix transfers to the existing returned-verdict trace. -/
theorem sizes_success [DecidableEq State] [DecidableEq Symbol]
    (rows : State → List (Row State Symbol Constraint)) (states : List State)
    (evaluates : Constraint × Term Symbol → Nat → SolverAdapter.Result → Prop)
    {bound result work} (run : SizesRun (ClassRun rows evaluates) states bound result work) :
    ∀ output, result = .ok output →
      SizesRun (SourceSizedDecided.ClassRun rows (returned evaluates)) states bound (.ok output) work := by
  induction run with
  | zero => intro output same; cases same; exact .zero
  | error prior ih => intro output impossible; cases impossible
  | next prior next ih =>
      intro output same
      exact .next (ih _ rfl) (states_success rows evaluates next output same)

/-- A state pass has a finite completed outcome, including either kind of stop. -/
theorem states_finite [DecidableEq State] [DecidableEq Symbol]
    (rows : State → List (Row State Symbol Constraint))
    (evaluates : Constraint × Term Symbol → Nat → SolverAdapter.Result → Prop)
    (completed : ∀ item, ∃ work result, evaluates item work result)
    (smaller : Table State (Term Symbol)) (size : Nat) (states : List State) (built : Table State (Term Symbol)) :
    ∃ result work, StatesRun (ClassRun rows evaluates) smaller size states built result work := by
  induction states generalizing built with
  | nil => exact ⟨.ok built, 0, .nil⟩
  | cons state rest ih =>
      obtain ⟨result, work, run⟩ := class_finite rows evaluates completed smaller size state
      cases result with
      | error bad => exact ⟨.error bad, work + 1, .error run⟩
      | ok terms =>
          obtain ⟨result, tailWork, tail⟩ := ih (insert built state size terms)
          exact ⟨result, work + tailWork + 1, .ok run tail⟩

/-- The whole size fold has a finite outcome without excluding exceptions. -/
theorem sizes_finite [DecidableEq State] [DecidableEq Symbol]
    (rows : State → List (Row State Symbol Constraint)) (states : List State)
    (evaluates : Constraint × Term Symbol → Nat → SolverAdapter.Result → Prop)
    (completed : ∀ item, ∃ work result, evaluates item work result) (bound : Nat) :
    ∃ result work, SizesRun (ClassRun rows evaluates) states bound result work := by
  induction bound with
  | zero => exact ⟨.ok (fun _ _ => []), 0, .zero⟩
  | succ bound ih =>
      obtain ⟨result, work, run⟩ := ih
      cases result with
      | error bad => exact ⟨.error bad, work + 1, .error run⟩
      | ok smaller =>
          obtain ⟨result, nextWork, next⟩ := states_finite rows evaluates completed smaller (bound + 1) states smaller
          exact ⟨result, work + nextWork + 1, .next run next⟩

/-- Class failure identifies the first stopping candidate before deduplication. -/
theorem class_first_stop [DecidableEq Symbol] (rows : State → List (Row State Symbol Constraint))
    (evaluates : Constraint × Term Symbol → Nat → SolverAdapter.Result → Prop)
    {smaller size state result work} (run : ClassRun rows evaluates smaller size state result work) :
    ∀ bad, result = .error bad → ∃ before item after accepted beforeWork stopWork,
      pairs rows smaller size state = before ++ item :: after ∧
      SourceSizedDecidedFilter.Run (returned evaluates) before (.ok accepted) beforeWork ∧
      Caused evaluates bad item stopWork := by
  cases run with
  | @done filtered filterWork finished =>
      intro bad same
      cases filtered with
      | error error =>
          have equal : error = bad := Except.error.inj same
          subst bad
          exact filter_first_stop evaluates finished error rfl
      | ok accepted => simp [Except.map] at same

/-- The first stop follows successful size, state, and candidate prefixes in source order. -/
theorem sizes_first_stop [DecidableEq State] [DecidableEq Symbol]
    (rows : State → List (Row State Symbol Constraint)) (states : List State)
    (evaluates : Constraint × Term Symbol → Nat → SolverAdapter.Result → Prop)
    {bound result work} (run : SizesRun (ClassRun rows evaluates) states bound result work) :
    ∀ bad, result = .error bad → ∃ earlier smaller sizeWork, earlier < bound ∧
      SizesRun (SourceSizedDecided.ClassRun rows (returned evaluates)) states earlier (.ok smaller) sizeWork ∧
      ∃ beforeStates state afterStates intermediate stateWork,
        states = beforeStates ++ state :: afterStates ∧
        StatesRun (SourceSizedDecided.ClassRun rows (returned evaluates)) smaller (earlier + 1)
          beforeStates smaller (.ok intermediate) stateWork ∧
        ∃ beforeTerms item afterTerms accepted termWork stopWork,
          pairs rows smaller (earlier + 1) state = beforeTerms ++ item :: afterTerms ∧
          SourceSizedDecidedFilter.Run (returned evaluates) beforeTerms (.ok accepted) termWork ∧
          Caused evaluates bad item stopWork := by
  intro bad same
  obtain ⟨earlier, smaller, sizeWork, passWork, below, sizes, failedPass⟩ :=
    SourceSizedDecidedOperational.sizes_first_error _ run bad same
  obtain ⟨beforeStates, state, afterStates, intermediate, stateWork, classWork, statesEq, statesRun, failedClass⟩ :=
    SourceSizedDecidedOperational.states_first_error _ failedPass bad rfl
  obtain ⟨beforeTerms, item, afterTerms, accepted, termWork, stopWork, termsEq, terms, stopped⟩ :=
    class_first_stop rows evaluates failedClass bad rfl
  exact ⟨earlier, smaller, sizeWork, below, sizes_success rows states evaluates sizes _ rfl,
    beforeStates, state, afterStates, intermediate, stateWork, statesEq,
    states_success rows evaluates statesRun _ rfl,
    beforeTerms, item, afterTerms, accepted, termWork, stopWork, termsEq, terms, stopped⟩

end MicroCFTA.SourceSizedLiquidExecution
