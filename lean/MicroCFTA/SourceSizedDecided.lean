import MicroCFTA.SourceSizedDecidedExecution
import MicroCFTA.SourceSizedReference

/-!
# Solver-decided exact size classes

The row list is the source sorted row list. The processed state list is the
source trim key list. The guard evaluator and the constraint meaning remain
explicit parameters. Unknown retains the original constraint and term.

Successful tables agree in order with the reference on the processed graph.
Connecting that graph to the original root language requires the trim
adapter to preserve acceptance. No interned construction or pruning is used.
-/

namespace MicroCFTA.SourceSizedDecided

open Language RecursiveSize SourceSizedDecidedTable

/-- A source transition retains its original constraint for evaluation and errors. -/
structure Row (State Symbol Constraint : Type) where
  label : Symbol
  children : List State
  constraint : Constraint

/-- Interpret one original transition constraint on the complete term. -/
def Row.edge (holds : Constraint → Term Symbol → Bool)
    (row : Row State Symbol Constraint) : Edge State Symbol :=
  ⟨row.label, row.children, holds row.constraint⟩

/-- Interpret the source row lists without changing their order. -/
def automaton (rows : State → List (Row State Symbol Constraint))
    (holds : Constraint → Term Symbol → Bool) : Automaton State Symbol :=
  fun state => (rows state).map (Row.edge holds)

/-- Retain rows only at the states whose classes are built. -/
def selected [DecidableEq State] (states : List State) (A : Automaton State Symbol) :
    Automaton State Symbol := fun state => if state ∈ states then A state else []

/-- Preserve transition-major and candidate order, including repeated pairs. -/
def pairs (rows : State → List (Row State Symbol Constraint))
    (smaller : Table State (Term Symbol)) (size : Nat) (state : State) :
    List (Constraint × Term Symbol) :=
  (rows state).flatMap fun row =>
    (SourceSizedCandidates.candidates smaller row.label row.children size).map
      fun term => (row.constraint, term)

/-- Keep each accepted term at its first occurrence after all guards are checked. -/
def finish [DecidableEq Symbol] (accepted : List (Constraint × Term Symbol)) : List (Term Symbol) :=
  SourceSizedReference.nub (accepted.map Prod.snd)

/-- Decide every candidate constraint, then remove duplicate accepted terms. -/
def make [DecidableEq Symbol] (rows : State → List (Row State Symbol Constraint))
    (answer : Constraint × Term Symbol → Guards.Verdict)
    (smaller : Table State (Term Symbol)) (size : Nat) (state : State) :
    Except (Constraint × Term Symbol) (List (Term Symbol)) :=
  (SourceSizedDecidedFilter.filter answer (pairs rows smaller size state)).map finish

/-- The source bounded fold produces all classes through the requested bound. -/
def sizedUpTo [DecidableEq State] [DecidableEq Symbol]
    (rows : State → List (Row State Symbol Constraint)) (states : List State)
    (answer : Constraint × Term Symbol → Guards.Verdict) (bound : Nat) :
    Except (Constraint × Term Symbol) (Table State (Term Symbol)) :=
  upTo (make rows answer) states bound

/-- A nonpositive source bound performs no size pass. -/
def sizedUpToSigned [DecidableEq State] [DecidableEq Symbol]
    (rows : State → List (Row State Symbol Constraint)) (states : List State)
    (answer : Constraint × Term Symbol → Guards.Verdict) (bound : Int) :
    Except (Constraint × Term Symbol) (Table State (Term Symbol)) :=
  sizedUpTo rows states answer bound.toNat

/-- Nonpositive bounds return the empty table without calling the evaluator. -/
theorem sizedUpToSigned_nonpositive [DecidableEq State] [DecidableEq Symbol]
    (rows : State → List (Row State Symbol Constraint)) (states : List State)
    (answer : Constraint × Term Symbol → Guards.Verdict) (bound : Int) (nonpositive : bound ≤ 0) :
    sizedUpToSigned rows states answer bound = .ok (fun _ _ => []) := by
  simp [sizedUpToSigned, Int.toNat_of_nonpos nonpositive, sizedUpTo, upTo]

/-- A successful class is the reference class in exactly the same order. -/
theorem make_exact [DecidableEq Symbol]
    (rows : State → List (Row State Symbol Constraint))
    (answer : Constraint × Term Symbol → Guards.Verdict)
    (holds : Constraint → Term Symbol → Bool)
    (adequate : SourceSizedDecidedFilter.Adequate answer (fun pair => holds pair.1 pair.2))
    (smaller : Table State (Term Symbol)) (size : Nat) (state : State)
    (output : List (Term Symbol)) (success : make rows answer smaller size state = .ok output) :
    output = SourceSizedReference.classOf smaller (automaton rows holds state) size := by
  cases result : SourceSizedDecidedFilter.filter answer (pairs rows smaller size state) with
  | error error => simp [make, result, Except.map] at success
  | ok accepted =>
      have same : finish accepted = output := by simpa [make, result, Except.map] using success
      rw [← same, SourceSizedDecidedFilter.success_exact answer
        (fun pair => holds pair.1 pair.2) adequate _ _ result]
      simp [finish, pairs, SourceSizedReference.classOf, automaton, Row.edge,
        List.filter_flatMap, List.filter_map, List.map_flatMap, List.map_map,
        List.flatMap_map, Function.comp_def]

/-- The error is the first Unknown constraint-term pair, before deduplication. -/
theorem make_error_iff [DecidableEq Symbol]
    (rows : State → List (Row State Symbol Constraint))
    (answer : Constraint × Term Symbol → Guards.Verdict)
    (smaller : Table State (Term Symbol)) (size : Nat) (state : State)
    (bad : Constraint × Term Symbol) :
    make rows answer smaller size state = .error bad ↔
      ∃ before after, pairs rows smaller size state = before ++ bad :: after ∧
        (∀ item ∈ before, answer item ≠ .unknown) ∧ answer bad = .unknown := by
  have same : make rows answer smaller size state = .error bad ↔
      SourceSizedDecidedFilter.filter answer (pairs rows smaller size state) = .error bad := by
    cases result : SourceSizedDecidedFilter.filter answer (pairs rows smaller size state) <;>
      simp [make, result, Except.map]
  exact same.trans (SourceSizedDecidedFilter.error_iff answer _ bad)

/-- Failure preserves the first Unknown in size, state, then candidate order. -/
theorem sizedUpTo_error_iff [DecidableEq State] [DecidableEq Symbol]
    (rows : State → List (Row State Symbol Constraint)) (states : List State)
    (answer : Constraint × Term Symbol → Guards.Verdict) (bound : Nat)
    (bad : Constraint × Term Symbol) :
    sizedUpTo rows states answer bound = .error bad ↔
      ∃ earlier smaller, earlier < bound ∧ sizedUpTo rows states answer earlier = .ok smaller ∧
        ∃ beforeStates state afterStates intermediate,
          states = beforeStates ++ state :: afterStates ∧
          addStates (make rows answer) smaller (earlier + 1) beforeStates smaller = .ok intermediate ∧
          ∃ beforeTerms afterTerms,
            pairs rows smaller (earlier + 1) state = beforeTerms ++ bad :: afterTerms ∧
            (∀ item ∈ beforeTerms, answer item ≠ .unknown) ∧ answer bad = .unknown := by
  simp only [sizedUpTo, upTo_error_iff, addStates_error_iff, make_error_iff]

/-- An evaluator with no Unknown answers produces a successful bounded table. -/
theorem sizedUpTo_success [DecidableEq State] [DecidableEq Symbol]
    (rows : State → List (Row State Symbol Constraint)) (states : List State)
    (answer : Constraint × Term Symbol → Guards.Verdict)
    (decides : ∀ pair, answer pair ≠ .unknown) (bound : Nat) :
    ∃ output, sizedUpTo rows states answer bound = .ok output := by
  apply upTo_success (make rows answer) ?_ states bound
  intro smaller size state
  let accepted := (pairs rows smaller size state).filter (fun pair => answer pair == .yes)
  have result : SourceSizedDecidedFilter.filter answer (pairs rows smaller size state) = .ok accepted :=
    (SourceSizedDecidedFilter.success_iff answer _ accepted).mpr ⟨fun pair _ => decides pair, rfl⟩
  exact ⟨finish accepted, by simp [make, result, Except.map]⟩

/-- A state excluded from the finite table has no reference class in the selected graph. -/
theorem selected_absent [DecidableEq State] [DecidableEq Symbol]
    (states : List State) (A : Automaton State Symbol) (state : State)
    (absent : state ∉ states) (size : Nat) :
    SourceSizedReference.classes (selected states A) size state = [] := by
  cases size with
  | zero => exact SourceSizedReference.classes_zero _ _
  | succ remaining =>
      simp [SourceSizedReference.classes_succ, selected, absent,
        SourceSizedReference.classOf, SourceSizedReference.nub, RefinementValidation.dedup]

/-- Successful bounded tables agree with the reference sequence on the selected graph. -/
theorem sizedUpTo_exact [DecidableEq State] [DecidableEq Symbol]
    (rows : State → List (Row State Symbol Constraint)) (states : List State)
    (answer : Constraint × Term Symbol → Guards.Verdict)
    (holds : Constraint → Term Symbol → Bool)
    (adequate : SourceSizedDecidedFilter.Adequate answer (fun pair => holds pair.1 pair.2))
    (bound : Nat) (output : Table State (Term Symbol))
    (success : sizedUpTo rows states answer bound = .ok output) :
    Matches states (SourceSizedReference.classes (selected states (automaton rows holds))) bound output := by
  apply upTo_exact (make rows answer) states
    (SourceSizedReference.classes (selected states (automaton rows holds))) ?_ bound output success
  intro previous smaller matched state present terms done
  rw [make_exact rows answer holds adequate smaller (previous + 1) state terms done,
    SourceSizedReference.classes_succ]
  have sameRows : selected states (automaton rows holds) state = automaton rows holds state := by
    simp [selected, present]
  rw [sameRows]
  apply SourceSizedReference.classOf_congr
  intro child size below
  rw [matched]
  by_cases included : child ∈ states
  · by_cases positive : 0 < size
    · simp [included, positive, show size ≤ previous by omega]
    · have zero : size = 0 := by omega
      subst size
      simp [SourceSizedReference.classes_zero]
  · simp [included, selected_absent states (automaton rows holds) child included size]

/-- Every accepted output has exactly its requested node-count size. -/
theorem sizedUpTo_member_iff [DecidableEq State] [DecidableEq Symbol]
    (rows : State → List (Row State Symbol Constraint)) (states : List State)
    (answer : Constraint × Term Symbol → Guards.Verdict)
    (holds : Constraint → Term Symbol → Bool)
    (adequate : SourceSizedDecidedFilter.Adequate answer (fun pair => holds pair.1 pair.2))
    (bound : Nat) (output : Table State (Term Symbol))
    (success : sizedUpTo rows states answer bound = .ok output)
    (state : State) (size : Nat) (term : Term Symbol) :
    term ∈ output state size ↔ state ∈ states ∧ 0 < size ∧ size ≤ bound ∧
      Accepts (selected states (automaton rows holds)) state term ∧ nodeSize term = size := by
  rw [sizedUpTo_exact rows states answer holds adequate bound output success state size]
  split
  next domain => simp [SourceSizedReference.mem_classes_iff, domain.1, domain.2.1, domain.2.2]
  next outside =>
    simp only [List.not_mem_nil, false_iff, not_and]
    intro present positive below _ _
    exact outside ⟨present, positive, below⟩

/-- Each successful class contains distinct terms. -/
theorem sizedUpTo_nodup [DecidableEq State] [DecidableEq Symbol]
    (rows : State → List (Row State Symbol Constraint)) (states : List State)
    (answer : Constraint × Term Symbol → Guards.Verdict)
    (holds : Constraint → Term Symbol → Bool)
    (adequate : SourceSizedDecidedFilter.Adequate answer (fun pair => holds pair.1 pair.2))
    (bound : Nat) (output : Table State (Term Symbol))
    (success : sizedUpTo rows states answer bound = .ok output) (state : State) (size : Nat) :
    (output state size).Nodup := by
  rw [sizedUpTo_exact rows states answer holds adequate bound output success state size]
  split
  · exact SourceSizedReference.classes_nodup _ _ _
  · exact List.nodup_nil

/-- An above-bound class is empty regardless of evaluator adequacy. -/
theorem sizedUpTo_above [DecidableEq State] [DecidableEq Symbol]
    (rows : State → List (Row State Symbol Constraint)) (states : List State)
    (answer : Constraint × Term Symbol → Guards.Verdict)
    (bound : Nat) (output : Table State (Term Symbol))
    (success : sizedUpTo rows states answer bound = .ok output)
    (state : State) (size : Nat) (larger : bound < size) : output state size = [] :=
  upTo_above (make rows answer) states bound output success state size larger

/-- A class trace records all completed evaluator calls before term deduplication. -/
inductive ClassRun [DecidableEq Symbol]
    (rows : State → List (Row State Symbol Constraint))
    (evaluates : Constraint × Term Symbol → Nat → Guards.Verdict → Prop)
    (smaller : Table State (Term Symbol)) (size : Nat) (state : State) :
    Except (Constraint × Term Symbol) (List (Term Symbol)) → Nat → Prop where
  | done : SourceSizedDecidedFilter.Run evaluates (pairs rows smaller size state) result work →
      ClassRun rows evaluates smaller size state (result.map finish) (work + 1)

/-- Terminating external evaluations imply a finite run for each class call. -/
theorem class_finite [DecidableEq Symbol]
    (rows : State → List (Row State Symbol Constraint))
    (evaluates : Constraint × Term Symbol → Nat → Guards.Verdict → Prop)
    (answer : Constraint × Term Symbol → Guards.Verdict)
    (terminates : SourceSizedDecidedFilter.Terminates evaluates answer)
    (smaller : Table State (Term Symbol)) (size : Nat) (state : State) :
    ∃ work, ClassRun rows evaluates smaller size state (make rows answer smaller size state) work := by
  obtain ⟨work, finished⟩ := SourceSizedDecidedFilter.finite_execution evaluates answer terminates
    (pairs rows smaller size state)
  exact ⟨work + 1, .done finished⟩

/-- Every finite bound finishes when the external evaluator finishes every call. -/
theorem sizedUpTo_finite [DecidableEq State] [DecidableEq Symbol]
    (rows : State → List (Row State Symbol Constraint)) (states : List State)
    (evaluates : Constraint × Term Symbol → Nat → Guards.Verdict → Prop)
    (answer : Constraint × Term Symbol → Guards.Verdict)
    (terminates : SourceSizedDecidedFilter.Terminates evaluates answer) (bound : Nat) :
    ∃ work, SourceSizedDecidedExecution.SizesRun (ClassRun rows evaluates) states bound
      (sizedUpTo rows states answer bound) work :=
  SourceSizedDecidedExecution.sizes_finite (make rows answer) (ClassRun rows evaluates)
    (class_finite rows evaluates answer terminates) states bound

/-- A deterministic external trace returns the modeled source class result. -/
theorem class_result [DecidableEq Symbol]
    (rows : State → List (Row State Symbol Constraint))
    (evaluates : Constraint × Term Symbol → Nat → Guards.Verdict → Prop)
    (answer : Constraint × Term Symbol → Guards.Verdict)
    (agrees : ∀ pair work verdict, evaluates pair work verdict → answer pair = verdict)
    {smaller size state result work} (run : ClassRun rows evaluates smaller size state result work) :
    make rows answer smaller size state = result := by
  cases run with
  | done finished =>
      unfold make
      rw [SourceSizedDecidedFilter.run_result evaluates answer agrees finished]

/-- A deterministic external trace returns the modeled source bounded result. -/
theorem sizedUpTo_result [DecidableEq State] [DecidableEq Symbol]
    (rows : State → List (Row State Symbol Constraint)) (states : List State)
    (evaluates : Constraint × Term Symbol → Nat → Guards.Verdict → Prop)
    (answer : Constraint × Term Symbol → Guards.Verdict)
    (agrees : ∀ pair work verdict, evaluates pair work verdict → answer pair = verdict)
    {bound result work}
    (run : SourceSizedDecidedExecution.SizesRun (ClassRun rows evaluates) states bound result work) :
    sizedUpTo rows states answer bound = result :=
  SourceSizedDecidedExecution.sizes_result (make rows answer) (ClassRun rows evaluates)
    (fun _ _ _ _ _ finished => class_result rows evaluates answer agrees finished) run

end MicroCFTA.SourceSizedDecided
