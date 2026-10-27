/-- Depth induction discharges the complete original-input contract at every finite recursive capacity. -/
theorem finite_complete
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveFuel : Nat) :
    Complete (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver recursiveFuel := by
  induction recursiveFuel with
  | zero =>
      intro inventory caller memos before metadata seed ceiling packet bounded known
        _selectionMembers _selectionLength _initialMass _reserved
      obtain ⟨outcome, running, resources⟩ := resume_zero_outcome_resources
        holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver inventory
        caller memos before metadata (SourcePruningEnumerationRestart.decision stop order metadata before)
        seed packet bounded known
      exact ⟨0, outcome, fun extra => by simpa only [run, Nat.zero_add] using running extra, resources⟩
  | succ recursiveFuel ih =>
      intro inventory caller memos before metadata seed ceiling packet bounded known
        selectionMembers selectionLength initialMass reserved
      exact run_finite_succ_complete_resources
        holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver recursiveFuel ih
        inventory caller memos before metadata seed ceiling packet bounded known
        selectionMembers selectionLength initialMass reserved

/-- Original packets and a finite original reservation derive the actual stable recursive result. -/
theorem run_finite_complete_resources
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (recursiveFuel : Nat) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (metadata : Metadata Typing)
    (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (initialMass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (reserved : SourcePruningEnumerationFiniteReservation.Reserved bits recursiveFuel seed ceiling) :
    ∃ bound outcome,
      (∀ extra, run holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel
        metadata caller memos.query before = outcome) ∧
      OutcomeResources formulas solver caller
        (SourcePruningEnumerationFiniteReservation.final recursiveFuel seed ceiling) outcome :=
  finite_complete holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver recursiveFuel
    inventory caller memos before metadata seed ceiling packet bounded known
    selectionMembers selectionLength initialMass reserved
