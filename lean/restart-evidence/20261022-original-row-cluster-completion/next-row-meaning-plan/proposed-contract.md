# Proposed prose contract: row_inputs_meaning
Target module: SourceCurrentOriginalRowPhysicalMeaning.lean. One public theorem: row_inputs_meaning.
This is a prose contract only. It is not an exact Lean declaration or implementation.
Use the existing concrete Symbol = SourceObservations.Label FullSyntax.Formula and Guard = SourceSymbolicIndex.Constraint FullSyntax.Formula.
The existing ContextCache.RowLanguage fixes these types through its local notation. A generic Symbol/Guard conclusion cannot reuse that declaration literally (S01).
Quantify an arbitrary holds : Guard → Term Symbol → Bool. No Formulas, solver or solver contract is needed.
Quantify one source constructor state and actual InternedNestedFacts.Facts for that same source.
Quantify inputModel : InputMeaning (SourceRecursiveIntersectionInputView.view source holds). Keep this exact model throughout.
Quantify one actual parent Value and one actual EdgeValue row.
Require OriginalInput source (inputOf parent), Available source parent, and parent.free = [].
Require inputModel.valid (inputOf parent). This is structural model admission, not a desired result-language law.
Require literal membership row ∈ InternedEdgeResidency.nodeEdges parent. No symbol-group or same-symbol comparison premise is needed.
Conclude BOTH of the following statements.
First: for every child in row.children, Original child and inputModel.valid (inputOf child). This is exactly one side of EdgeInputs.
Second: for every ambient InternedGuardedLanguage.Env, RowLanguage holds inputModel.languages row equals InternedGuardedLanguage.edgeMeaning holds ambient row as languages.
The equality uses the literal row symbol, complete guard and ordered child payloads. It includes both directions for every finite term.
No width, machine, state extension, cache, Stable, Contextual, native request, fuel, completion, future readiness, Room or successful execution premise belongs in this pure adapter.
No RankedInput, rank-erasure or completeness assumption is required. InputMeaning.copy_exact and row_valid already suffice.
No desired child meaning, row language equality, total exact meet or comparison callback may be supplied as a premise.
Canonical InputInventoryModels.root_valid can discharge the parent-admission premise separately for a fixed closed original inventory (S13).
The theorem must not replace an arbitrary populated cache model. A later stateful caller keeps its existing admitted source/model packet.
