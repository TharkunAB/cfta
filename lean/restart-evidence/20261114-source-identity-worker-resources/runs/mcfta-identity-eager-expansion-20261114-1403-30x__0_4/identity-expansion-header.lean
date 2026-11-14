private theorem identity_eager_expansion_resources
    (graph : Graph Symbol Constraint)
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat)
    (recursive : EagerResumeWithNarrowComplete (Typing := Unit) (bits := bits)
      (fun _ _ _ node state => .done node state) graph [] checkEmpty edgesOf
      none (fun _ _ => none) formulas solver recursiveDepth)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (metadata : Metadata Unit)
    (uv : Nat) (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (initialMass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (reserved : eagerReserved bits (recursiveDepth + 1) seed ceiling)
    (chosen : SourcePruningEnumerationRestart.decision none (fun _ _ => none) metadata before = some (.expand uv)) :
    ∃ fuel outcome,
      (∀ extra, SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow
        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
          (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
        (fun _ _ _ node state => .done node state) graph [] checkEmpty edgesOf
        none (fun _ _ => none) (fuel + extra) (recursiveDepth + 1)
        metadata caller memos.query before (some (.expand uv)) = outcome) ∧
      OutcomeResources formulas solver caller (eagerFinal (recursiveDepth + 1) seed ceiling) outcome
