theorem output_done_frontier
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original : Caller width) (seed : Seed) (output : Output width Typing)
    (resources : OutputResources formulas solver original seed output)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (origin : OutputOrigin stop order output) (completed : output.metadata = none) :
    ∀ (uv handle : Nat) (scs : List Suspended),
      output.cache.core.values[uv]? = some (.unenumerated (some handle) scs) →
        ∃ value, SourcePruningEnumerationNodes.lookupNode output.caller.checked.native.machine.heap handle = some value ∧
          InternedProbeProvenance.Available output.caller.checked.native.machine.heap value ∧ value.free = [] ∧
          MergedOrdinaryHeight.recursiveBoundary value = true ∧ scs = [] := by
