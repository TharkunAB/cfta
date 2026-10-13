import MicroCFTA.SourceSizedPreprocessing
import MicroCFTA.SourceSizedDecidedQueries

/-!
# Canonical preprocessing and the public decided Sized worker

The state inventory comes from the original structural trim. Candidate rows
come from the actual canonical sorting of the original graph. No row-order
premise is needed. Guards are evaluated on each complete candidate term.
-/

namespace MicroCFTA.SourceSizedDecidedPublic

open Language RecursiveSize SourceSizedPreprocessing SourceSizedDecided
open SourceSizedDecidedTable SourceSizedDecidedTrim SourceSizedDecidedOrder
open Std
attribute [local instance] lexOrd

/-- The source decides exactly the original structural trim keys, including its root. -/
def reached [DecidableEq State] (input : Input State Symbol Constraint) : List State :=
  trimKeys input.states (automaton input.rows (fun _ _ => true)) input.root

/-- The source state inventory does not depend on a constraint interpretation. -/
theorem reached_interpretation [DecidableEq State] (input : Input State Symbol Constraint)
    (holds : Constraint → Term Symbol → Bool) :
    reached input = trimKeys input.states (automaton input.rows holds) input.root := by
  unfold reached trimKeys
  rw [SourceSizedTrimGuards.productive_independent input.rows input.states (fun _ _ => true) holds,
    SourceSizedTrimGuards.live_successors_independent input.rows input.states (fun _ _ => true) holds]

/-- Run the source signed bounded query with actual canonical rows and original trim keys. -/
def publicSizedUpTo [DecidableEq State] [DecidableEq Symbol] [Ord Symbol]
    (input : Input State Symbol Constraint)
    (answer : Constraint × Term Symbol → Guards.Verdict) (bound : Int) :
    Except (Constraint × Term Symbol) (Table State (Term Symbol)) :=
  sizedUpToSigned (sortedRows input) (reached input) answer bound

/-- The structural public fold is the interpreted fold used by the exactness theorem. -/
theorem public_eq_interpreted [DecidableEq State] [DecidableEq Symbol] [Ord Symbol]
    (input : Input State Symbol Constraint)
    (answer : Constraint × Term Symbol → Guards.Verdict) (bound : Int)
    (holds : Constraint → Term Symbol → Bool) :
    publicSizedUpTo input answer bound =
      sizedUpTo (sortedRows input) (trimKeys input.states (automaton input.rows holds) input.root)
        answer bound.toNat := by
  simp only [publicSizedUpTo, sizedUpToSigned, reached_interpretation input holds]

/-- Original full-guard acceptance and node count exactly describe each successful public class. -/
theorem public_member_iff [DecidableEq State] [DecidableEq Symbol] [Ord Symbol]
    (input : Input State Symbol Constraint)
    (answer : Constraint × Term Symbol → Guards.Verdict) (bound : Int)
    (holds : Constraint → Term Symbol → Bool)
    (adequate : SourceSizedDecidedFilter.Adequate answer (fun pair => holds pair.1 pair.2))
    (output : Table State (Term Symbol)) (success : publicSizedUpTo input answer bound = .ok output)
    (size : Nat) (term : Term Symbol) :
    term ∈ output input.root size ↔
      Accepts (automaton input.rows holds) input.root term ∧ nodeSize term = size ∧ (size : Int) ≤ bound := by
  rw [public_eq_interpreted input answer bound holds] at success
  rw [sizedUpTo_original_iff input.states input.complete (automaton input.rows holds)
    (sortedRows input) answer holds (fun state => (sortedRows_perm input state).map _) adequate
    input.root bound.toNat output success]
  have positive := nodeSize_pos term
  constructor <;> rintro ⟨accepted, exactSize, within⟩ <;> exact ⟨accepted, exactSize, by omega⟩

/-- The source signed class query is exact for the original guarded language. -/
theorem public_signed_member_iff [DecidableEq State] [DecidableEq Symbol] [Ord Symbol]
    (input : Input State Symbol Constraint)
    (answer : Constraint × Term Symbol → Guards.Verdict) (bound : Int)
    (holds : Constraint → Term Symbol → Bool)
    (adequate : SourceSizedDecidedFilter.Adequate answer (fun pair => holds pair.1 pair.2))
    (output : Table State (Term Symbol)) (success : publicSizedUpTo input answer bound = .ok output)
    (size : Int) (term : Term Symbol) :
    term ∈ SourceSizedQueries.termsSigned (output input.root) size ↔
      Accepts (automaton input.rows holds) input.root term ∧ (nodeSize term : Int) = size ∧ size ≤ bound := by
  unfold SourceSizedQueries.termsSigned
  split
  next nonpositive =>
    have positive := nodeSize_pos term
    constructor
    · simp
    · rintro ⟨_, exactSize, _⟩
      omega
  next positive =>
    rw [public_member_iff input answer bound holds adequate output success]
    have nonnegative : 0 ≤ size := by omega
    have castSize := Int.toNat_of_nonneg nonnegative
    constructor <;> rintro ⟨accepted, exactSize, within⟩ <;> exact ⟨accepted, by omega, by omega⟩

/-- Successful public classes retain the exact canonical first-occurrence sequence. -/
theorem public_reference_order [DecidableEq State] [DecidableEq Symbol] [Ord Symbol]
    (input : Input State Symbol Constraint)
    (answer : Constraint × Term Symbol → Guards.Verdict) (bound : Int)
    (holds : Constraint → Term Symbol → Bool)
    (adequate : SourceSizedDecidedFilter.Adequate answer (fun pair => holds pair.1 pair.2))
    (output : Table State (Term Symbol)) (success : publicSizedUpTo input answer bound = .ok output)
    (size : Nat) :
    output input.root size = if size ≤ bound.toNat then
      SourceSizedReference.classes (automaton (sortedRows input) holds) size input.root else [] := by
  rw [public_eq_interpreted input answer bound holds] at success
  exact sizedUpTo_reference_order input.states input.complete (automaton input.rows holds)
    (sortedRows input) answer holds (fun state => (sortedRows_perm input state).map _) adequate
    input.root bound.toNat output success size

/-- Nonpositive public bounds perform no evaluator calls and return the empty table. -/
theorem public_nonpositive [DecidableEq State] [DecidableEq Symbol] [Ord Symbol]
    (input : Input State Symbol Constraint)
    (answer : Constraint × Term Symbol → Guards.Verdict) (bound : Int) (nonpositive : bound ≤ 0) :
    publicSizedUpTo input answer bound = .ok (fun _ _ => []) :=
  sizedUpToSigned_nonpositive (sortedRows input) (reached input) answer bound nonpositive

/-- The public fold finishes if each external evaluation finishes. -/
theorem public_finite [DecidableEq State] [DecidableEq Symbol] [Ord Symbol]
    (input : Input State Symbol Constraint)
    (evaluates : Constraint × Term Symbol → Nat → Guards.Verdict → Prop)
    (answer : Constraint × Term Symbol → Guards.Verdict)
    (terminates : SourceSizedDecidedFilter.Terminates evaluates answer) (bound : Int) :
    ∃ work, SourceSizedDecidedExecution.SizesRun (ClassRun (sortedRows input) evaluates)
      (reached input) bound.toNat (publicSizedUpTo input answer bound) work :=
  sizedUpTo_finite (sortedRows input) (reached input) evaluates answer terminates bound.toNat

/-- Canonical refinement and the bounded evaluated fold both have finite completion witnesses. -/
theorem public_preprocessing_and_execution [DecidableEq State] [DecidableEq Symbol] [Ord Symbol]
    (input : Input State Symbol Constraint)
    (evaluates : Constraint × Term Symbol → Nat → Guards.Verdict → Prop)
    (answer : Constraint × Term Symbol → Guards.Verdict)
    (terminates : SourceSizedDecidedFilter.Terminates evaluates answer) (bound : Int) :
    ∃ classes work, CanonicalClasses.canonical (graph input) = some classes ∧
      sortedRows input = sortRows input classes ∧
      SourceSizedDecidedExecution.SizesRun (ClassRun (sortedRows input) evaluates)
        (reached input) bound.toNat (publicSizedUpTo input answer bound) work := by
  obtain ⟨classes, completed, sorted⟩ := sortedRows_completed input
  obtain ⟨work, executed⟩ := public_finite input evaluates answer terminates bound
  exact ⟨classes, work, completed, sorted, executed⟩

/-- Public failure is the first Unknown in ascending size, original trim-key, then canonical candidate order. -/
theorem public_error_iff [DecidableEq State] [DecidableEq Symbol] [Ord Symbol]
    (input : Input State Symbol Constraint)
    (answer : Constraint × Term Symbol → Guards.Verdict) (bound : Int)
    (bad : Constraint × Term Symbol) :
    publicSizedUpTo input answer bound = .error bad ↔
      ∃ earlier smaller, earlier < bound.toNat ∧
        sizedUpTo (sortedRows input) (reached input) answer earlier = .ok smaller ∧
        ∃ beforeStates state afterStates intermediate,
          reached input = beforeStates ++ state :: afterStates ∧
          addStates (make (sortedRows input) answer) smaller (earlier + 1) beforeStates smaller = .ok intermediate ∧
          ∃ beforeTerms afterTerms,
            pairs (sortedRows input) smaller (earlier + 1) state = beforeTerms ++ bad :: afterTerms ∧
            (∀ item ∈ beforeTerms, answer item ≠ .unknown) ∧ answer bad = .unknown :=
  sizedUpTo_error_iff (sortedRows input) (reached input) answer bound.toNat bad

end MicroCFTA.SourceSizedDecidedPublic
