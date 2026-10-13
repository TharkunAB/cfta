import MicroCFTA.SourceRowsMinimum
import MicroCFTA.SymbolicGraphView

/-!
# Minimum sizes ignore payloads and labels

Only the ordered child lists enter the recurrence. Constraint replacement
and symbol relabeling therefore leave every sweep and the converged table
unchanged. State renaming preserves minimum sizes through exact row readback.
-/

namespace MicroCFTA.SourceRowsMinimumShape

open Language MinimumSize SymbolicGraphView

/-- The source row arithmetic on child lists alone. -/
def row (known : State → Option Nat) : List (List State) → Option Nat
  | [] => none
  | children :: rest => best ((childSum known children).map (· + 1)) (row known rest)

/-- Symbols and guards do not occur in the actual transition minimum. -/
theorem row_shape (known : State → Option Nat) (edges : List (Edge State Symbol)) :
    rowMinimum known edges = row known (edges.map Edge.children) := by
  induction edges with
  | nil => rfl
  | cons edge rest ih => simp only [rowMinimum, edgeMinimum, List.map_cons, row, ih]

/-- Equal child lists make every right-fold source sweep identical. -/
theorem sweep_shape [DecidableEq State] (first : Automaton State First) (second : Automaton State Second)
    (same : ∀ state, (first state).map Edge.children = (second state).map Edge.children)
    (keys : List State) (known : State → Option Nat) : sweep first keys known = sweep second keys known := by
  induction keys with
  | nil => rfl
  | cons key rest ih =>
      change relax first key (sweep first rest known) = relax second key (sweep second rest known)
      rw [ih]
      funext state
      simp [relax, row_shape, same key]

/-- Payload and label changes preserve every finite sweep prefix, not only its final fixed point. -/
theorem sweeps_shape [DecidableEq State] (first : Automaton State First) (second : Automaton State Second)
    (same : ∀ state, (first state).map Edge.children = (second state).map Edge.children)
    (keys : List State) (fuel : Nat) (known : State → Option Nat) :
    sweeps first keys fuel known = sweeps second keys fuel known := by
  induction fuel generalizing known with
  | zero => rfl
  | succ fuel ih => simp only [sweeps, sweep_shape first second same, ih]

/-- The actual finite convergence recursion is independent of constraint and symbol payloads. -/
theorem converge_shape [DecidableEq State] (first : Automaton State First) (second : Automaton State Second)
    (same : ∀ state, (first state).map Edge.children = (second state).map Edge.children)
    (keys : List State) (known : State → Option Nat) :
    SourceRowsMinimum.converge first keys known = SourceRowsMinimum.converge second keys known := by
  induction known using SourceRowsMinimum.converge.induct first keys with
  | case1 known next stable =>
      dsimp only [next] at stable
      rw [SourceRowsMinimum.converge.eq_def, SourceRowsMinimum.converge.eq_def]
      rw [← sweep_shape first second same]
      simp only [dite_eq_left stable]
  | case2 known next unstable ih =>
      dsimp only [next] at unstable
      rw [SourceRowsMinimum.converge.eq_def, SourceRowsMinimum.converge.eq_def]
      rw [← sweep_shape first second same]
      simp only [dite_eq_right unstable]
      exact ih

/-- Table.minimumSizes is invariant under arbitrary transition payload changes. -/
theorem minimum_shape [DecidableEq State] (first : Automaton State First) (second : Automaton State Second)
    (same : ∀ state, (first state).map Edge.children = (second state).map Edge.children) (keys : List State) :
    SourceRowsMinimum.minimumSizes first keys = SourceRowsMinimum.minimumSizes second keys :=
  converge_shape first second same keys (fun _ => none)

/-- Exact accepted language equality fixes the computed minimum independently of key order. -/
theorem minimum_language [DecidableEq Source] [DecidableEq Target]
    (source : Automaton Source Symbol) (target : Automaton Target Symbol)
    (sourcePlain : Decoder.Plain source) (targetPlain : Decoder.Plain target)
    (sourceKeys : List Source) (targetKeys : List Target)
    (sourceSupport : SourceRowsMinimum.Supported source sourceKeys)
    (targetSupport : SourceRowsMinimum.Supported target targetKeys)
    (sourceState : Source) (targetState : Target)
    (same : ∀ term, Accepts source sourceState term ↔ Accepts target targetState term) :
    SourceRowsMinimum.minimumSizes source sourceKeys sourceState =
      SourceRowsMinimum.minimumSizes target targetKeys targetState := by
  cases found : SourceRowsMinimum.minimumSizes source sourceKeys sourceState with
  | none =>
      have empty := (SourceRowsMinimum.none_iff source sourcePlain sourceKeys sourceSupport sourceState).mp found
      exact ((SourceRowsMinimum.none_iff target targetPlain targetKeys targetSupport targetState).mpr
        (fun term accepted => empty term ((same term).mpr accepted))).symm
  | some size =>
      have minimum := (SourceRowsMinimum.correct source sourcePlain sourceKeys sourceSupport sourceState size).mp found
      exact ((SourceRowsMinimum.correct target targetPlain targetKeys targetSupport targetState size).mpr
        ⟨let ⟨term, accepted, height⟩ := minimum.1; ⟨term, (same term).mp accepted, height⟩,
          fun term accepted => minimum.2 term ((same term).mpr accepted)⟩).symm

/-- Actual child-state relabeling preserves minima under the adapter's row readback equation. -/
theorem minimum_rename [DecidableEq Source] [DecidableEq Target]
    (source : Automaton Source Symbol) (target : Automaton Target Symbol) (rename : Source → Target)
    (readback : ∀ state, target (rename state) = (source state).map (renameEdge rename))
    (sourcePlain : Decoder.Plain source) (targetPlain : Decoder.Plain target)
    (sourceKeys : List Source) (targetKeys : List Target)
    (sourceSupport : SourceRowsMinimum.Supported source sourceKeys)
    (targetSupport : SourceRowsMinimum.Supported target targetKeys) (state : Source) :
    SourceRowsMinimum.minimumSizes source sourceKeys state = SourceRowsMinimum.minimumSizes target targetKeys (rename state) := by
  apply minimum_language source target sourcePlain targetPlain sourceKeys targetKeys sourceSupport targetSupport state (rename state)
  intro term
  exact (rowsCorrespond_exact source target rename (fun state edge => by rw [readback]; simp only [List.mem_map, eq_comm]) state term).symm

end MicroCFTA.SourceRowsMinimumShape
