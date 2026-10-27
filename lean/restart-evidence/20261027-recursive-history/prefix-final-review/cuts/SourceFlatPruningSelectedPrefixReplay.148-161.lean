/-- Replay the complete actual prefix from its retained old validity certificate. -/
theorem run_related_of_valid
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (fuel uv : Nat) (caller : Caller width) (before : OldCached) (flat : FlatCached) (memos : Memos)
    (related : EnumerationFlatCached.Related flat before)
    (valid : SourcePruningEnumerationSelectedStep.PrefixValid holeKey fits admits graph templates
      checkEmpty edgesOf stop order metadata formulas solver inventory fuel uv caller before memos
      (SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
        fuel fuel fuel fuel fuel fuel uv caller before memos.query)) :
    ResultRelated (run holeKey fits admits graph templates stop order metadata fuel fuel uv caller flat memos.query)
      (SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
        fuel fuel fuel fuel fuel fuel uv caller before memos.query) := by
