import MicroCFTA.Guards

/-!
# The ordered guard filter in `Data.CFTA.Sized.sizedUpTo`

The error retains the first candidate whose evaluator returns Unknown.
The finite execution theorem requires a finite completion witness for each
external evaluation. It does not prove termination of an external solver.
-/

namespace MicroCFTA.SourceSizedDecidedFilter

open Guards

/-- Keep Yes candidates, drop No candidates, and stop at the first Unknown. -/
def filter (answer : α → Verdict) : List α → Except α (List α)
  | [] => .ok []
  | item :: rest =>
      match answer item with
      | .unknown => .error item
      | .no => filter answer rest
      | .yes => (filter answer rest).map (item :: ·)

/-- A successful filter has no Unknown and retains exactly the Yes subsequence. -/
theorem success_iff (answer : α → Verdict) (items output : List α) :
    filter answer items = .ok output ↔
      (∀ item ∈ items, answer item ≠ .unknown) ∧
        output = items.filter (fun item => answer item == .yes) := by
  induction items generalizing output with
  | nil => simp [filter]
  | cons item rest ih =>
      cases verdict : answer item with
      | unknown => simp [filter, verdict]
      | no => simp [filter, verdict, ih]
      | yes =>
          cases tail : filter answer rest with
          | error bad =>
              have missing : ¬ ∀ next ∈ rest, answer next ≠ .unknown := by
                intro decided
                have good := (ih (rest.filter (fun next => answer next == .yes))).mpr
                  ⟨decided, rfl⟩
                rw [tail] at good
                cases good
              simp [filter, Except.map, verdict, tail, missing]
          | ok kept =>
              obtain ⟨decided, same⟩ := (ih kept).mp tail
              have allDecided : ∀ next ∈ item :: rest, answer next ≠ .unknown := by
                simpa using And.intro (by simp [verdict] : answer item ≠ .unknown) decided
              constructor
              · intro success
                refine ⟨allDecided, ?_⟩
                simpa [filter, Except.map, verdict, tail, same, eq_comm] using success
              · rintro ⟨_, equal⟩
                simp [filter, Except.map, verdict, tail, same, equal]

/-- Failure identifies the first Unknown in the original candidate order. -/
theorem error_iff (answer : α → Verdict) (items : List α) (bad : α) :
    filter answer items = .error bad ↔
      ∃ before after, items = before ++ bad :: after ∧
        (∀ item ∈ before, answer item ≠ .unknown) ∧ answer bad = .unknown := by
  induction items with
  | nil => simp [filter]
  | cons item rest ih =>
      cases verdict : answer item with
      | unknown =>
          constructor
          · intro failed
            have same : item = bad := by simpa [filter, Except.map, verdict] using failed
            subst bad
            exact ⟨[], rest, rfl, by simp, verdict⟩
          · rintro ⟨before, after, same, decided, unknown⟩
            cases before with
            | nil =>
                have equal : item = bad := by simpa using congrArg List.head? same
                subst bad
                simp [filter, verdict]
            | cons first tail =>
                have equal : item = first := by simpa using congrArg List.head? same
                subst first
                exact False.elim ((decided item (by simp)) verdict)
      | no | yes =>
          have notUnknown : answer item ≠ .unknown := by simp [verdict]
          have step : filter answer (item :: rest) = .error bad ↔
              filter answer rest = .error bad := by
            cases result : filter answer rest <;> simp [filter, Except.map, verdict, result]
          rw [step, ih]
          constructor
          · rintro ⟨before, after, same, decided, unknown⟩
            exact ⟨item :: before, after, by simp [same],
              by simpa using And.intro notUnknown decided, unknown⟩
          · rintro ⟨before, after, same, decided, unknown⟩
            cases before with
            | nil =>
                have equal : item = bad := by simpa using congrArg List.head? same
                subst bad
                exact False.elim (notUnknown unknown)
            | cons first tail =>
                have equal : rest = tail ++ bad :: after := by
                  simpa using congrArg List.tail same
                exact ⟨tail, after, equal, fun next present => decided next (by simp [present]), unknown⟩

/-- A decided evaluator result agrees with the Boolean term semantics. -/
def Adequate (answer : α → Verdict) (holds : α → Bool) : Prop :=
  ∀ item, Supports (answer item) (holds item = true)

/-- Success agrees with the pure guard filter under evaluator adequacy. -/
theorem success_exact (answer : α → Verdict) (holds : α → Bool)
    (adequate : Adequate answer holds) (items output : List α)
    (success : filter answer items = .ok output) : output = items.filter holds := by
  obtain ⟨decided, same⟩ := (success_iff answer items output).mp success
  rw [same]
  apply List.filter_congr
  intro item present
  have sound := adequate item
  cases verdict : answer item with
  | unknown => exact False.elim (decided item present verdict)
  | yes =>
      rw [verdict] at sound
      simp only [Supports] at sound
      simp [sound]
  | no =>
      rw [verdict] at sound
      simp only [Supports] at sound
      simp [Bool.eq_false_iff.mpr sound]

/-- A finite external evaluation trace followed by the source filter. -/
inductive Run (evaluates : α → Nat → Verdict → Prop) :
    List α → Except α (List α) → Nat → Prop where
  | nil : Run evaluates [] (.ok []) 0
  | unknown : evaluates item work .unknown →
      Run evaluates (item :: rest) (.error item) (work + 1)
  | no : evaluates item work .no → Run evaluates rest result tailWork →
      Run evaluates (item :: rest) result (work + tailWork + 1)
  | yesOk : evaluates item work .yes → Run evaluates rest (.ok kept) tailWork →
      Run evaluates (item :: rest) (.ok (item :: kept)) (work + tailWork + 1)
  | yesError : evaluates item work .yes → Run evaluates rest (.error bad) tailWork →
      Run evaluates (item :: rest) (.error bad) (work + tailWork + 1)

/-- Every candidate evaluation that is used must finish with the chosen verdict. -/
def Terminates (evaluates : α → Nat → Verdict → Prop) (answer : α → Verdict) : Prop :=
  ∀ item, ∃ work, evaluates item work (answer item)

/-- A finite candidate list finishes if each external evaluation finishes. -/
theorem finite_execution (evaluates : α → Nat → Verdict → Prop) (answer : α → Verdict)
    (terminates : Terminates evaluates answer) (items : List α) :
    ∃ work, Run evaluates items (filter answer items) work := by
  induction items with
  | nil => exact ⟨0, .nil⟩
  | cons item rest ih =>
      obtain ⟨work, completed⟩ := terminates item
      cases verdict : answer item with
      | unknown =>
          rw [verdict] at completed
          exact ⟨work + 1, by simpa [filter, Except.map, verdict] using Run.unknown (rest := rest) completed⟩
      | no =>
          rw [verdict] at completed
          obtain ⟨tailWork, tail⟩ := ih
          exact ⟨work + tailWork + 1, by simpa [filter, Except.map, verdict] using Run.no completed tail⟩
      | yes =>
          rw [verdict] at completed
          obtain ⟨tailWork, tail⟩ := ih
          cases result : filter answer rest with
          | ok kept =>
              rw [result] at tail
              exact ⟨work + tailWork + 1, by
                simpa [filter, Except.map, verdict, result] using Run.yesOk completed tail⟩
          | error bad =>
              rw [result] at tail
              exact ⟨work + tailWork + 1, by
                simpa [filter, Except.map, verdict, result] using Run.yesError completed tail⟩

/-- A deterministic evaluator trace returns the executable filter result. -/
theorem run_result (evaluates : α → Nat → Verdict → Prop) (answer : α → Verdict)
    (agrees : ∀ item work verdict, evaluates item work verdict → answer item = verdict)
    {items result work} (run : Run evaluates items result work) :
    filter answer items = result := by
  induction run with
  | nil => rfl
  | unknown completed => simp [filter, agrees _ _ _ completed]
  | no completed tail ih => simpa [filter, agrees _ _ _ completed] using ih
  | yesOk completed tail ih => simp [filter, Except.map, agrees _ _ _ completed, ih]
  | yesError completed tail ih => simp [filter, Except.map, agrees _ _ _ completed, ih]

end MicroCFTA.SourceSizedDecidedFilter
