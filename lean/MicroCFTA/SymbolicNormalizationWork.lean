import MicroCFTA.SymbolicWork

/-!
# Work does not increase during source normalization

The measure includes every context node and unresolved path step. Sorting,
deduplication, alpha-renaming, and path following cannot increase it. Finite
substitution work is supplied by the strict source binding budget.
-/
namespace MicroCFTA.SymbolicDriver
open Symbolic (Fragment Target Obligation)
open Language

/-- Work of one path existence or path equality requirement. -/
def obligationWork (weight : Nat → Nat) : Obligation Symbol → Nat
  | .exists target => targetWork weight target
  | .equal left right => targetWork weight left + targetWork weight right

/-- Total pending work; constructor decomposition does not add a per-equation cost. -/
def obligationsWork (weight : Nat → Nat) (requirements : List (Obligation Symbol)) : Nat :=
  (requirements.map (obligationWork weight)).sum

/-- A retained existence test uses no more work than its target. -/
theorem required_work (target : Target Symbol) :
    obligationsWork (fun _ => 1) (required target) ≤ targetWork (fun _ => 1) target := by
  unfold required
  split <;> simp [obligationsWork, obligationWork]

/-- The complete successful target-normalization path does not increase work. -/
theorem normalizeTarget_work (weight : Nat → Nat) (problem : Problem Symbol)
    (budget : BindingBudget weight problem.bindings) (names : List (Nat × Nat)) (fuel : Nat)
    (target output : Target Symbol) (success : normalizeTarget fuel problem names target = .ok (some output)) :
    targetWork (fun _ => 1) output ≤ targetWork weight target := by
  cases followed : follow problem.bindings fuel target.fragment target.path with
  | error error => simp only [normalizeTarget, followed] at success; cases success
  | ok result =>
      cases result with
      | none => simp only [normalizeTarget, followed] at success; cases success
      | some current =>
          cases renamed : rename names fuel current.fragment with
          | error error => simp only [normalizeTarget, followed, renamed, Bind.bind, Except.bind] at success; cases success
          | ok fragment =>
              simp only [normalizeTarget, followed, renamed, Bind.bind, Except.bind, Pure.pure, Except.pure] at success
              cases success
              have bounded := follow_work weight problem.bindings budget fuel target.fragment target.path current followed
              simpa only [targetWork, (rename_work names fuel).1 current.fragment fragment renamed] using bounded

/-- The source's self-equality and target-ordering rewrites do not increase requirement work. -/
theorem normalizeObligation_work [DecidableEq Symbol] [Ord Symbol]
    (weight : Nat → Nat) (problem : Problem Symbol) (budget : BindingBudget weight problem.bindings)
    (names : List (Nat × Nat)) (fuel : Nat) (requirement : Obligation Symbol)
    (output : Option (List (Obligation Symbol)))
    (success : normalizeObligation fuel problem names requirement = .ok output) :
    obligationsWork (fun _ => 1) (output.getD []) ≤ obligationWork weight requirement := by
  cases requirement with
  | «exists» target =>
      cases normalized : normalizeTarget fuel problem names target with
      | error error => simp only [normalizeObligation, normalized] at success; cases success
      | ok result =>
          cases result with
          | none =>
              simp only [normalizeObligation, normalized, Bind.bind, Except.bind, Option.map_none, Pure.pure, Except.pure] at success
              cases success
              exact Nat.zero_le _
          | some current =>
              simp only [normalizeObligation, normalized, Bind.bind, Except.bind, Option.map_some, Pure.pure, Except.pure] at success
              cases success
              exact Nat.le_trans (required_work current) (normalizeTarget_work weight problem budget names fuel target current normalized)
  | equal left right =>
      cases first : normalizeTarget fuel problem names left with
      | error error => simp only [normalizeObligation, first] at success; cases success
      | ok firstResult =>
          cases second : normalizeTarget fuel problem names right with
          | error error => simp only [normalizeObligation, first, second] at success; cases success
          | ok secondResult =>
              cases firstResult with
              | none =>
                  simp only [normalizeObligation, first, second, Bind.bind, Except.bind, Pure.pure, Except.pure] at success
                  cases success
                  exact Nat.zero_le _
              | some a =>
                  cases secondResult with
                  | none =>
                      simp only [normalizeObligation, first, second, Bind.bind, Except.bind, Pure.pure, Except.pure] at success
                      cases success
                      exact Nat.zero_le _
                  | some b =>
                      have firstBound := normalizeTarget_work weight problem budget names fuel left a first
                      have secondBound := normalizeTarget_work weight problem budget names fuel right b second
                      simp only [normalizeObligation, first, second, Bind.bind, Except.bind, Pure.pure, Except.pure] at success
                      split at success
                      · cases success
                        have bounded := required_work a
                        simp only [Option.getD_some, obligationWork]
                        omega
                      · split at success <;> cases success <;>
                          simp only [Option.getD_some, obligationsWork, List.map_cons, List.map_nil,
                            List.sum_cons, List.sum_nil, Nat.add_zero, obligationWork] <;> omega

/-- Filtering a list cannot increase a nonnegative additive measure. -/
theorem filter_work_le (weight : Value → Nat) (keep : Value → Bool) (values : List Value) :
    ((values.filter keep).map weight).sum ≤ (values.map weight).sum := by
  induction values with
  | nil => exact Nat.le_refl _
  | cons first rest ih =>
      simp only [List.filter_cons]
      split <;> simp only [List.map_cons, List.sum_cons] <;> omega

/-- The exact deduplication loop cannot increase a nonnegative additive measure. -/
theorem uniqueBy_work_le (same : Value → Value → Bool) (weight : Value → Nat) (values : List Value) :
    ((uniqueBy same values).map weight).sum ≤ (values.map weight).sum := by
  cases values with
  | nil => simp [uniqueBy]
  | cons first rest =>
      have recursive := uniqueBy_work_le same weight (rest.filter fun other => !same first other)
      have filtered := filter_work_le weight (fun other => !same first other) rest
      simp only [uniqueBy, List.map_cons, List.sum_cons]
      omega
termination_by values.length
decreasing_by
  exact Nat.lt_succ_of_le (List.length_filter_le ..)

/-- A pointwise bound for traversed outputs also bounds their complete flattened pending work. -/
theorem pending_work_le (weight : Nat → Nat) (requirements : List (Obligation Symbol))
    (pending : List (Option (List (Obligation Symbol))))
    (related : All₂ (fun requirement result => obligationsWork (fun _ => 1) (result.getD []) ≤ obligationWork weight requirement)
      requirements pending) :
    obligationsWork (fun _ => 1) (pending.flatMap fun result => result.getD []) ≤ obligationsWork weight requirements := by
  induction related with
  | nil => exact Nat.le_refl _
  | cons first rest ih =>
      simp only [obligationsWork, List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
      unfold obligationsWork at first ih
      omega

/-- Every successful actual normalization stays within its finite substitution and path work. -/
theorem normalize_work [DecidableEq Symbol] [Ord Symbol] (weight : Nat → Nat)
    (problem : Problem Symbol) (budget : BindingBudget weight problem.bindings) (fuel : Nat)
    (normalized : Problem Symbol) (success : normalize fuel problem = .ok (some normalized)) :
    obligationsWork (fun _ => 1) normalized.obligations ≤ obligationsWork weight problem.obligations := by
  let names := problem.domains.zipIdx.map fun (entry, new) => (entry.1, new)
  cases results : problem.obligations.mapM (normalizeObligation fuel problem names) with
  | error error =>
      dsimp only [names] at results
      simp only [normalize, results] at success
      cases success
  | ok pending =>
      have related := mapM_success_all₂ (normalizeObligation fuel problem names) problem.obligations pending results
      have bounded := pending_work_le weight problem.obligations pending
        (related.imp fun requirement output succeeds => normalizeObligation_work weight problem budget names fuel requirement output succeeds)
      dsimp only [names] at results
      simp only [normalize, results] at success
      change (if pending.any Option.isNone then Except.ok none else
        Except.ok (some ⟨problem.domains.zipIdx.map (fun (entry, new) => (new, entry.2)), [], problem.domains.length,
          (uniqueBy obligationEq (pending.flatMap fun result => result.getD [])).mergeSort
            (fun left right => compareObligation left right != .gt)⟩)) = (Except.ok (some normalized) : Except Error _) at success
      split at success
      · cases success
      · cases success
        have reduced := uniqueBy_work_le obligationEq (obligationWork (fun _ => 1)) (pending.flatMap fun result => result.getD [])
        have sorted := ((List.mergeSort_perm (uniqueBy obligationEq (pending.flatMap fun result => result.getD []))
          (fun left right => compareObligation left right != .gt)).map (obligationWork (fun _ => 1))).sum_nat
        unfold obligationsWork at bounded ⊢
        exact Nat.le_trans (Nat.le_of_eq sorted) (Nat.le_trans reduced bounded)

end MicroCFTA.SymbolicDriver
