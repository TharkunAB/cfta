def CompleteWithHistory
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveFuel : Nat) : Prop :=
  ∀ (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
    (metadata : Metadata Typing) (seed : Seed) (ceiling : Nat),
    Packet formulas solver inventory caller memos metadata before →
    Fits seed.2 caller.checked →
    Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap →
    (∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows) →
    (∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length) →
    SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling →
    SourcePruningEnumerationFiniteReservation.Reserved bits recursiveFuel seed ceiling →
    ∃ bound outcome,
      (∀ extra, run holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel
        metadata caller memos.query before = outcome) ∧
      OutcomeResources formulas solver caller
        (SourcePruningEnumerationFiniteReservation.final recursiveFuel seed ceiling) outcome ∧
      ∀ extra output, output ∈ SourcePruningEnumerationHookInvocation.hookOutputs outcome →
        ResourceHistory holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver
          (bound + extra) recursiveFuel inventory caller memos metadata before seed ceiling
          (SourcePruningEnumerationRestart.decision stop order metadata before) output

/-- Forgetting history retains the original chosen bound and outcome. -/
theorem CompleteWithHistory.forget
    {holeKey : Typing → Nat → Key} {fits : Key → Symbol → Bool} {admits : Key → Node → Bool}
    {graph : Graph Symbol Constraint} {templates : List (Template.Pattern Symbol)}
    {checkEmpty : Bool} {edgesOf : Node → List (EdgeValue Symbol Constraint)}
    {stop : Option (Metadata Typing → Nat → Bool)} {order : Metadata Typing → List Nat → Option Nat}
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {recursiveFuel : Nat}
    (complete : CompleteWithHistory (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver recursiveFuel) :
    Complete (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver recursiveFuel := by
  intro inventory caller memos before metadata seed ceiling packet bounded known
    selectionMembers selectionLength mass reserved
  obtain ⟨bound, outcome, running, resources, _histories⟩ := complete
    inventory caller memos before metadata seed ceiling packet bounded known
    selectionMembers selectionLength mass reserved
  exact ⟨bound, outcome, running, resources⟩

/-- The actual zero-depth stop and done routes already have admitted output histories. -/
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

end MicroCFTA.SourcePruningEnumerationRecursive
