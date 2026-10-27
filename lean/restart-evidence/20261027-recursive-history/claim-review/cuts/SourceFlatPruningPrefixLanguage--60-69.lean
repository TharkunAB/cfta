theorem related_prefix_meaning
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (fuel uv : Nat) (caller : Caller width) (before : OldCached) (flat : FlatCached)
    (input : EnumerationFlatCached.Related flat before)
    (observed : Result width Typing)
    (earlier : SourcePruningEnumerationSelectedStep.Result width Typing)
    (related : ResultRelated observed earlier)
    (meaning : SourcePruningEnumerationSelectedStep.PrefixMeaning formulas solver fuel uv caller before earlier) :
    PrefixMeaning formulas solver fuel uv caller before flat observed := by
