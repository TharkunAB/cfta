import MicroCFTA.SourceSizedDeterminizationSourceLoop

/-!
# Source-loop evaluations and checking rounds

The relation records the known set, holder lists, accumulated table,
and current found batch. Each constructor counts one limit check.
The computed compile fuel bounds these checking rounds. It does not
bound tuple generation work, native heap use, or machine integers.
-/
namespace MicroCFTA.SourceSizedDeterminizationSourceEvaluation
open Language SourceSizedDeterminizationKernel SourceSizedDeterminizationDiscovery Std
open SourceSizedDeterminizationSourceLoop (go)
attribute [local instance] lexOrd

variable {State Symbol : Type} [DecidableEq State] [DecidableEq Symbol]
  [Ord State] [Ord Symbol]

/-- Record the literal source-loop states without a supplied recursion fuel. -/
inductive Evaluation (limit : Nat) (states : List State) (rows : Automaton State Symbol) :
    List (List State) → (State → List (List State)) →
      List (Choice State Symbol) → List (Choice State Symbol) → Nat →
        Outcome (List State) (List (Choice State Symbol)) → Prop where
  | limit_exceeded
      (over : limit < (CanonicalClasses.sortedSet (known ++
        fresh known (SourceSizedDeterminizationOrderedRun.foundKeys states rows found))).length) :
      Evaluation limit states rows known holding table found 1 .limitExceeded
  | done
      (within : (CanonicalClasses.sortedSet (known ++
        fresh known (SourceSizedDeterminizationOrderedRun.foundKeys states rows found))).length ≤ limit)
      (empty : fresh known (SourceSizedDeterminizationOrderedRun.foundKeys states rows found) = []) :
      Evaluation limit states rows known holding table found 1
        (.ready (CanonicalClasses.sortedSet (known ++
          fresh known (SourceSizedDeterminizationOrderedRun.foundKeys states rows found))) (table ++ found))
  | next
      (within : (CanonicalClasses.sortedSet (known ++
        fresh known (SourceSizedDeterminizationOrderedRun.foundKeys states rows found))).length ≤ limit)
      (nonempty : fresh known (SourceSizedDeterminizationOrderedRun.foundKeys states rows found) ≠ [])
      (following :
        let new := fresh known (SourceSizedDeterminizationOrderedRun.foundKeys states rows found)
        let more := CanonicalClasses.sortedSet (known ++ new)
        let updated := SourceSizedDeterminizationHolderInsertion.update holding new
        Evaluation limit states rows more updated (table ++ found)
          (SourceSizedDeterminizationOrderedStep.round states rows new updated more) calls result) :
      Evaluation limit states rows known holding table found (calls + 1) result

/-- Every terminal bounded execution has at most fuel plus one checking rounds. -/
theorem go_evaluates (limit : Nat) (states : List State) (rows : Automaton State Symbol)
    (fuel : Nat) (known : List (List State)) (holding : State → List (List State))
    (table found : List (Choice State Symbol))
    (terminal : go limit states rows fuel known holding table found ≠ .exhausted) :
    ∃ calls, calls ≤ fuel + 1 ∧
      Evaluation limit states rows known holding table found calls
        (go limit states rows fuel known holding table found) := by
  revert terminal
  induction fuel generalizing known holding table found with
  | zero =>
    intro terminal
    let new := fresh known (SourceSizedDeterminizationOrderedRun.foundKeys states rows found)
    let more := CanonicalClasses.sortedSet (known ++ new)
    by_cases over : limit < more.length
    · rw [go, ite_eq_left over]
      exact ⟨1, by omega, Evaluation.limit_exceeded over⟩
    · by_cases empty : new = []
      · rw [go, ite_eq_right over, ite_eq_left empty]
        exact ⟨1, by omega, Evaluation.done (Nat.le_of_not_gt over) empty⟩
      · rw [go, ite_eq_right over, ite_eq_right empty] at terminal
        exact False.elim (terminal rfl)
  | succ remaining ih =>
    intro terminal
    let new := fresh known (SourceSizedDeterminizationOrderedRun.foundKeys states rows found)
    let more := CanonicalClasses.sortedSet (known ++ new)
    by_cases over : limit < more.length
    · rw [go, ite_eq_left over]
      exact ⟨1, by omega, Evaluation.limit_exceeded over⟩
    · by_cases empty : new = []
      · rw [go, ite_eq_right over, ite_eq_left empty]
        exact ⟨1, by omega, Evaluation.done (Nat.le_of_not_gt over) empty⟩
      · rw [go, ite_eq_right over, ite_eq_right empty] at terminal ⊢
        dsimp only at terminal ⊢
        obtain ⟨calls, bounded, execution⟩ := ih more
          (SourceSizedDeterminizationHolderInsertion.update holding new) (table ++ found)
          (SourceSizedDeterminizationOrderedStep.round states rows new
            (SourceSizedDeterminizationHolderInsertion.update holding new) more) terminal
        exact ⟨calls + 1, by omega, Evaluation.next (Nat.le_of_not_gt over) empty execution⟩

variable [TransOrd State] [LawfulEqOrd State]

/-- The actual compile input derives terminal source evaluation from its original limit. -/
theorem compile_complete (limit : Nat) (states : List State) (rows : Automaton State Symbol) :
    ∃ calls, calls ≤ limit + 1 ∧
      Evaluation limit states rows [] (fun _ => []) []
        (SourceSizedDeterminizationOrderedRun.initial states rows) calls
        (SourceSizedDeterminizationSourceLoop.compile limit states rows) :=
  go_evaluates limit states rows limit [] (fun _ => []) []
    (SourceSizedDeterminizationOrderedRun.initial states rows)
    (SourceSizedDeterminizationSourceLoop.compile_terminal limit states rows)

/-- The public 1024-key branch uses at most 1025 source-loop checking rounds. -/
theorem sized_complete (states : List State) (rows : Automaton State Symbol) :
    ∃ calls, calls ≤ 1025 ∧
      Evaluation 1024 states rows [] (fun _ => []) []
        (SourceSizedDeterminizationOrderedRun.initial states rows) calls
        (SourceSizedDeterminizationSourceLoop.compile 1024 states rows) :=
  compile_complete 1024 states rows

end MicroCFTA.SourceSizedDeterminizationSourceEvaluation
