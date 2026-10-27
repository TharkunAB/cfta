theorem zero_complete_with_history
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    CompleteWithHistory (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver 0 := by
  intro inventory caller memos before metadata seed ceiling packet bounded known
    _selectionMembers _selectionLength mass reserved
  obtain ⟨outcome, running, resources⟩ := resume_zero_outcome_resources
    holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver inventory caller memos before metadata
    (SourcePruningEnumerationRestart.decision stop order metadata before) seed packet bounded known
  have admission : HistoryAdmission formulas solver inventory caller memos metadata before 0 seed ceiling :=
    ⟨packet, bounded, known, mass, reserved⟩
  refine ⟨0, outcome, ?_, resources, ?_⟩
  · intro extra
    exact running (0 + extra)
  · intro extra output member
    have emitted : output ∈ SourcePruningEnumerationHookInvocation.hookOutputs
        (run holeKey fits admits graph templates checkEmpty edgesOf stop order (0 + extra) 0
          metadata caller memos.query before) := by
      change output ∈ SourcePruningEnumerationHookInvocation.hookOutputs
        (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (0 + extra) 0
          metadata caller memos.query before (SourcePruningEnumerationRestart.decision stop order metadata before))
      rw [running (0 + extra)]
      exact member
    unfold run at emitted
    cases chosen : SourcePruningEnumerationRestart.decision stop order metadata before with
    | none =>
        rw [chosen] at emitted
        simp only [resume, SourcePruningEnumerationHookInvocation.hookOutputs, List.mem_singleton] at emitted
        subst output
        exact .stopped admission
    | some next =>
        rw [chosen] at emitted
        cases next with
        | done =>
            simp only [resume, SourcePruningEnumerationHookInvocation.hookOutputs, List.mem_singleton] at emitted
            subst output
            exact .done admission
        | stuck | expand _ => cases emitted
