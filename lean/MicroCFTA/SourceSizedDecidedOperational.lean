import MicroCFTA.SourceSizedDecidedPublic

/-!
# Decided Sized execution with nondeterministic evaluator replies

Each call can return a different verdict, including on a repeated pair.
Successful traces need only adequacy of each returned verdict. Unknown
stops that trace and retains its original constraint-term pair. No fixed
reply function or deterministic evaluator is assumed.
-/

namespace MicroCFTA.SourceSizedDecidedOperational

open Language Guards SourceSizedDecided SourceSizedDecidedTable
open SourceSizedDecidedExecution SourceSizedDecidedPublic SourceSizedPreprocessing

/-- Every returned decided verdict agrees with the complete term semantics. -/
def Adequate (evaluates : α → Nat → Verdict → Prop) (holds : α → Bool) : Prop :=
  ∀ item work verdict, evaluates item work verdict → Supports verdict (holds item = true)

/-- Every call has some finite completed result; repeated calls need not agree. -/
def Terminates (evaluates : α → Nat → Verdict → Prop) : Prop :=
  ∀ item, ∃ work verdict, evaluates item work verdict

/-- The ideal decision is used only to compare successful traces with the pure table. -/
def ideal (holds : α → Bool) (item : α) : Verdict := if holds item then .yes else .no

/-- Ideal replies agree with their defining semantics. -/
theorem ideal_adequate (holds : α → Bool) : SourceSizedDecidedFilter.Adequate (ideal holds) holds := by
  intro item
  cases result : holds item <;> simp [ideal, result, Supports]

/-- A successful relational filter retains exactly the semantically true subsequence. -/
theorem filter_success (evaluates : α → Nat → Verdict → Prop) (holds : α → Bool)
    (adequate : Adequate evaluates holds) {items result work}
    (run : SourceSizedDecidedFilter.Run evaluates items result work) :
    ∀ output, result = .ok output → output = items.filter holds := by
  induction run with
  | nil => intro output same; simpa using (Except.ok.inj same).symm
  | unknown completed => intro output impossible; cases impossible
  | no completed tail ih =>
      intro output same
      have falseGuard := adequate _ _ _ completed
      have rejected : holds _ = false := Bool.eq_false_iff.mpr falseGuard
      simpa [rejected] using ih output same
  | yesOk completed tail ih =>
      intro output same
      have trueGuard : holds _ = true := adequate _ _ _ completed
      rw [← Except.ok.inj same]
      simp [trueGuard, ih _ rfl]
  | yesError completed tail ih => intro output impossible; cases impossible

/-- A successful class trace agrees with an ideal pure class, without deterministic actual replies. -/
theorem class_success [DecidableEq Symbol]
    (rows : State → List (Row State Symbol Constraint))
    (evaluates : Constraint × Term Symbol → Nat → Verdict → Prop)
    (holds : Constraint → Term Symbol → Bool)
    (adequate : Adequate evaluates (fun pair => holds pair.1 pair.2))
    {smaller size state result work} (run : ClassRun rows evaluates smaller size state result work) :
    ∀ output, result = .ok output →
      make rows (ideal (fun pair => holds pair.1 pair.2)) smaller size state = .ok output := by
  cases run with
  | @done filtered filterWork finished =>
      intro output same
      cases filtered with
      | error bad => simp [Except.map] at same
      | ok accepted =>
          have actual := filter_success evaluates (fun pair => holds pair.1 pair.2) adequate finished accepted rfl
          have idealRun : SourceSizedDecidedFilter.filter (ideal (fun pair => holds pair.1 pair.2))
              (pairs rows smaller size state) = .ok accepted := by
            apply (SourceSizedDecidedFilter.success_iff _ _ _).mpr
            refine ⟨?_, ?_⟩
            · intro pair _
              cases verdict : holds pair.1 pair.2 <;> simp [ideal, verdict]
            · rw [actual]
              apply List.filter_congr
              intro pair _
              cases verdict : holds pair.1 pair.2 <;> simp [ideal, verdict]
          simpa [make, idealRun, Except.map] using same

/-- Every successful relational state pass agrees with the ideal pure pass. -/
theorem states_success [DecidableEq State] [DecidableEq Symbol]
    (rows : State → List (Row State Symbol Constraint))
    (evaluates : Constraint × Term Symbol → Nat → Verdict → Prop)
    (holds : Constraint → Term Symbol → Bool)
    (adequate : Adequate evaluates (fun pair => holds pair.1 pair.2))
    {smaller size states built result work}
    (run : StatesRun (ClassRun rows evaluates) smaller size states built result work) :
    ∀ output, result = .ok output →
      addStates (make rows (ideal (fun pair => holds pair.1 pair.2))) smaller size states built = .ok output := by
  induction run with
  | nil => intro output same; exact same
  | error completed => intro output impossible; cases impossible
  | ok completed tail ih =>
      intro output same
      simpa [addStates, class_success rows evaluates holds adequate completed _ rfl] using ih output same

/-- Every successful relational bounded run has the same table as ideal decisions. -/
theorem sizes_success [DecidableEq State] [DecidableEq Symbol]
    (rows : State → List (Row State Symbol Constraint)) (states : List State)
    (evaluates : Constraint × Term Symbol → Nat → Verdict → Prop)
    (holds : Constraint → Term Symbol → Bool)
    (adequate : Adequate evaluates (fun pair => holds pair.1 pair.2))
    {bound result work} (run : SizesRun (ClassRun rows evaluates) states bound result work) :
    ∀ output, result = .ok output →
      sizedUpTo rows states (ideal (fun pair => holds pair.1 pair.2)) bound = .ok output := by
  induction run with
  | zero => intro output same; exact same
  | error prior ih => intro output impossible; cases impossible
  | next prior next ih =>
      intro output same
      simpa [sizedUpTo, upTo, show upTo (make rows (ideal (fun pair => holds pair.1 pair.2))) states _ = .ok _
        from ih _ rfl] using states_success rows evaluates holds adequate next output same

/-- Any successful public trace accepts exactly the original full guarded terms at each size. -/
theorem public_member_iff [DecidableEq State] [DecidableEq Symbol] [Ord Symbol]
    (input : Input State Symbol Constraint)
    (evaluates : Constraint × Term Symbol → Nat → Verdict → Prop)
    (holds : Constraint → Term Symbol → Bool)
    (adequate : Adequate evaluates (fun pair => holds pair.1 pair.2))
    (bound : Int) (output : Table State (Term Symbol)) (work : Nat)
    (run : SizesRun (ClassRun (sortedRows input) evaluates) (reached input) bound.toNat (.ok output) work)
    (size : Nat) (term : Term Symbol) :
    term ∈ output input.root size ↔ Accepts (automaton input.rows holds) input.root term ∧
      RecursiveSize.nodeSize term = size ∧ (size : Int) ≤ bound :=
  SourceSizedDecidedPublic.public_member_iff input (ideal (fun pair => holds pair.1 pair.2)) bound holds
    (ideal_adequate _) output
    (sizes_success (sortedRows input) (reached input) evaluates holds adequate run output rfl) size term

/-- Any successful public trace retains the exact canonical reference sequence. -/
theorem public_reference_order [DecidableEq State] [DecidableEq Symbol] [Ord Symbol]
    (input : Input State Symbol Constraint)
    (evaluates : Constraint × Term Symbol → Nat → Verdict → Prop)
    (holds : Constraint → Term Symbol → Bool)
    (adequate : Adequate evaluates (fun pair => holds pair.1 pair.2))
    (bound : Int) (output : Table State (Term Symbol)) (work : Nat)
    (run : SizesRun (ClassRun (sortedRows input) evaluates) (reached input) bound.toNat (.ok output) work)
    (size : Nat) :
    output input.root size = if size ≤ bound.toNat then
      SourceSizedReference.classes (automaton (sortedRows input) holds) size input.root else [] :=
  SourceSizedDecidedPublic.public_reference_order input (ideal (fun pair => holds pair.1 pair.2)) bound holds
    (ideal_adequate _) output
    (sizes_success (sortedRows input) (reached input) evaluates holds adequate run output rfl) size

/-- Finite candidate filtering needs completion of each call, not a fixed reply function. -/
theorem filter_finite (evaluates : α → Nat → Verdict → Prop)
    (terminates : Terminates evaluates) (items : List α) :
    ∃ result work, SourceSizedDecidedFilter.Run evaluates items result work := by
  induction items with
  | nil => exact ⟨.ok [], 0, .nil⟩
  | cons item rest ih =>
      obtain ⟨work, verdict, completed⟩ := terminates item
      cases verdict with
      | unknown => exact ⟨.error item, work + 1, .unknown completed⟩
      | no =>
          obtain ⟨result, tailWork, tail⟩ := ih
          exact ⟨result, work + tailWork + 1, .no completed tail⟩
      | yes =>
          obtain ⟨result, tailWork, tail⟩ := ih
          cases result with
          | error bad => exact ⟨.error bad, work + tailWork + 1, .yesError completed tail⟩
          | ok accepted => exact ⟨.ok (item :: accepted), work + tailWork + 1, .yesOk completed tail⟩

/-- Every class has a finite completed result under per-call completion. -/
theorem class_finite [DecidableEq Symbol]
    (rows : State → List (Row State Symbol Constraint))
    (evaluates : Constraint × Term Symbol → Nat → Verdict → Prop)
    (terminates : Terminates evaluates) (smaller : Table State (Term Symbol)) (size : Nat) (state : State) :
    ∃ result work, ClassRun rows evaluates smaller size state result work := by
  obtain ⟨result, work, run⟩ := filter_finite evaluates terminates (pairs rows smaller size state)
  exact ⟨result.map finish, work + 1, .done run⟩

/-- A finite state pass finishes, and propagates the exact pair of any Unknown error. -/
theorem states_finite [DecidableEq State] [DecidableEq Symbol]
    (rows : State → List (Row State Symbol Constraint))
    (evaluates : Constraint × Term Symbol → Nat → Verdict → Prop)
    (terminates : Terminates evaluates) (smaller : Table State (Term Symbol)) (size : Nat)
    (states : List State) (built : Table State (Term Symbol)) :
    ∃ result work, StatesRun (ClassRun rows evaluates) smaller size states built result work := by
  induction states generalizing built with
  | nil => exact ⟨.ok built, 0, .nil⟩
  | cons state rest ih =>
      obtain ⟨result, work, run⟩ := class_finite rows evaluates terminates smaller size state
      cases result with
      | error bad => exact ⟨.error bad, work + 1, .error run⟩
      | ok terms =>
          obtain ⟨result, tailWork, tail⟩ := ih (insert built state size terms)
          exact ⟨result, work + tailWork + 1, .ok run tail⟩

/-- Every finite bound has a completed result under per-call completion. -/
theorem sizes_finite [DecidableEq State] [DecidableEq Symbol]
    (rows : State → List (Row State Symbol Constraint)) (states : List State)
    (evaluates : Constraint × Term Symbol → Nat → Verdict → Prop)
    (terminates : Terminates evaluates) (bound : Nat) :
    ∃ result work, SizesRun (ClassRun rows evaluates) states bound result work := by
  induction bound with
  | zero => exact ⟨.ok (fun _ _ => []), 0, .zero⟩
  | succ bound ih =>
      obtain ⟨result, work, run⟩ := ih
      cases result with
      | error bad => exact ⟨.error bad, work + 1, .error run⟩
      | ok smaller =>
          obtain ⟨result, nextWork, next⟩ := states_finite rows evaluates terminates smaller (bound + 1) states smaller
          exact ⟨result, work + nextWork + 1, .next run next⟩

/-- The public signed bounded query has some finite result without deterministic replies. -/
theorem public_finite [DecidableEq State] [DecidableEq Symbol] [Ord Symbol]
    (input : Input State Symbol Constraint)
    (evaluates : Constraint × Term Symbol → Nat → Verdict → Prop)
    (terminates : Terminates evaluates) (bound : Int) :
    ∃ result work, SizesRun (ClassRun (sortedRows input) evaluates) (reached input) bound.toNat result work :=
  sizes_finite (sortedRows input) (reached input) evaluates terminates bound.toNat

/-- A failed filter trace has a successful actual prefix followed by its first Unknown call. -/
theorem filter_first_unknown (evaluates : α → Nat → Verdict → Prop) {items result work}
    (run : SourceSizedDecidedFilter.Run evaluates items result work) :
    ∀ bad, result = .error bad → ∃ before after accepted beforeWork unknownWork,
      items = before ++ bad :: after ∧
      SourceSizedDecidedFilter.Run evaluates before (.ok accepted) beforeWork ∧
      evaluates bad unknownWork .unknown := by
  induction run with
  | nil => intro bad impossible; cases impossible
  | @unknown item work rest completed =>
      intro bad same
      cases Except.error.inj same
      exact ⟨[], rest, [], 0, work, rfl, .nil, completed⟩
  | @no item work rest result tailWork completed tail ih =>
      intro bad same
      obtain ⟨before, after, accepted, beforeWork, unknownWork, itemsEq, prior, unknown⟩ := ih bad same
      exact ⟨item :: before, after, accepted, work + beforeWork + 1, unknownWork,
        by simp [itemsEq], .no completed prior, unknown⟩
  | yesOk completed tail ih => intro bad impossible; cases impossible
  | @yesError item work rest bad tailWork completed tail ih =>
      intro error same
      obtain ⟨before, after, accepted, beforeWork, unknownWork, itemsEq, prior, unknown⟩ := ih error same
      exact ⟨item :: before, after, item :: accepted, work + beforeWork + 1, unknownWork,
        by simp [itemsEq], .yesOk completed prior, unknown⟩

/-- A class error retains the first actual Unknown pair before term deduplication. -/
theorem class_first_unknown [DecidableEq Symbol]
    (rows : State → List (Row State Symbol Constraint))
    (evaluates : Constraint × Term Symbol → Nat → Verdict → Prop)
    {smaller size state result work} (run : ClassRun rows evaluates smaller size state result work) :
    ∀ bad, result = .error bad → ∃ before after accepted beforeWork unknownWork,
      pairs rows smaller size state = before ++ bad :: after ∧
      SourceSizedDecidedFilter.Run evaluates before (.ok accepted) beforeWork ∧
      evaluates bad unknownWork .unknown := by
  cases run with
  | @done filtered filterWork finished =>
      intro bad same
      cases filtered with
      | error error =>
          have equal : error = bad := by simpa [Except.map] using same
          subst bad
          exact filter_first_unknown evaluates finished error rfl
      | ok accepted => simp [Except.map] at same

/-- A failed state pass has an actual successful prefix and then its first failed class. -/
theorem states_first_error [DecidableEq State]
    (classRun : Table State Value → Nat → State → Except Error (List Value) → Nat → Prop)
    {smaller size states built result work} (run : StatesRun classRun smaller size states built result work) :
    ∀ bad, result = .error bad → ∃ before state after intermediate beforeWork errorWork,
      states = before ++ state :: after ∧
      StatesRun classRun smaller size before built (.ok intermediate) beforeWork ∧
      classRun smaller size state (.error bad) errorWork := by
  induction run with
  | nil => intro bad impossible; cases impossible
  | @error state error work rest built completed =>
      intro bad same
      cases Except.error.inj same
      exact ⟨[], state, rest, built, 0, work, rfl, .nil, completed⟩
  | @ok state terms work rest built result tailWork completed tail ih =>
      intro bad same
      obtain ⟨before, failed, after, intermediate, beforeWork, errorWork, statesEq, prior, error⟩ := ih bad same
      exact ⟨state :: before, failed, after, intermediate, work + beforeWork + 1, errorWork,
        by simp [statesEq], .ok completed prior, error⟩

/-- A failed size fold has an actual successful prefix and then its first failed size pass. -/
theorem sizes_first_error [DecidableEq State]
    (classRun : Table State Value → Nat → State → Except Error (List Value) → Nat → Prop)
    {states bound result work} (run : SizesRun classRun states bound result work) :
    ∀ bad, result = .error bad → ∃ earlier smaller beforeWork errorWork,
      earlier < bound ∧ SizesRun classRun states earlier (.ok smaller) beforeWork ∧
      StatesRun classRun smaller (earlier + 1) states smaller (.error bad) errorWork := by
  induction run with
  | zero => intro bad impossible; cases impossible
  | error prior ih =>
      intro bad same
      obtain ⟨earlier, smaller, beforeWork, errorWork, below, prefixRun, errorRun⟩ := ih bad same
      exact ⟨earlier, smaller, beforeWork, errorWork, by omega, prefixRun, errorRun⟩
  | @next bound smaller work result nextWork prior next ih =>
      intro bad same
      exact ⟨bound, smaller, work, nextWork, by omega, prior, same ▸ next⟩

/-- A public failed trace preserves its first actual Unknown pair and all preceding successful prefixes. -/
theorem public_first_unknown [DecidableEq State] [DecidableEq Symbol] [Ord Symbol]
    (input : Input State Symbol Constraint)
    (evaluates : Constraint × Term Symbol → Nat → Verdict → Prop)
    (bound : Int) (bad : Constraint × Term Symbol) (work : Nat)
    (run : SizesRun (ClassRun (sortedRows input) evaluates) (reached input) bound.toNat (.error bad) work) :
    ∃ earlier smaller sizeWork, earlier < bound.toNat ∧
      SizesRun (ClassRun (sortedRows input) evaluates) (reached input) earlier (.ok smaller) sizeWork ∧
      ∃ beforeStates state afterStates intermediate stateWork,
        reached input = beforeStates ++ state :: afterStates ∧
        StatesRun (ClassRun (sortedRows input) evaluates) smaller (earlier + 1)
          beforeStates smaller (.ok intermediate) stateWork ∧
        ∃ beforeTerms afterTerms accepted termWork unknownWork,
          pairs (sortedRows input) smaller (earlier + 1) state = beforeTerms ++ bad :: afterTerms ∧
          SourceSizedDecidedFilter.Run evaluates beforeTerms (.ok accepted) termWork ∧
          evaluates bad unknownWork .unknown := by
  obtain ⟨earlier, smaller, sizeWork, passWork, below, sizes, failedPass⟩ :=
    sizes_first_error _ run bad rfl
  obtain ⟨beforeStates, state, afterStates, intermediate, stateWork, classWork, statesEq, states, failedClass⟩ :=
    states_first_error _ failedPass bad rfl
  obtain ⟨beforeTerms, afterTerms, accepted, termWork, unknownWork, termsEq, terms, unknown⟩ :=
    class_first_unknown _ _ failedClass bad rfl
  exact ⟨earlier, smaller, sizeWork, below, sizes, beforeStates, state, afterStates, intermediate,
    stateWork, statesEq, states, beforeTerms, afterTerms, accepted, termWork, unknownWork, termsEq, terms, unknown⟩

end MicroCFTA.SourceSizedDecidedOperational
