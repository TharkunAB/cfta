# Source main d44b2a0f and the Haskell fix handoff

Main `d44b2a0f` is merged at `b09f4ebb`. The merge retains all earlier
formalization commits and the optimized interned core. Conflicts affected
only duplicate comments and changelog text. Upstream wording is retained for
the shared typing fix. The separate constructor-repair changelog entry stays.

## Typing metadata

Upstream `b3f4de44` adopts the finite needed-type walk from local repair
`ca0e9a65`. The current `Typing.hs` matches main. Its new regression returns
`Right [Plain, Other]` despite an unused non-regular field. Helper declaration
order remains `Right [Lit Z, Lit A]`. The existing helper-order proofs retain
the same executable algorithm. Generic, codec, and full rank correspondence
retain their documented adapters.

## Synthesis ordering and refold edges

`refoldEdges` returns the refolded root and a function from an input edge to
its rebuilt edge. It uses the same recursive-unfolding inventory as `refold`.
Each changed round composes its child-rebuilding function with the earlier
edge map. General termination, concrete memoization, and runtime edge-map
correspondence still need source adapters.

Synthesis introduces `Space`, `reduceWithOrder`, and `orderedSpace`.
Program enumeration takes a `Space`. The order uses the first reduction round
that reaches an edge. Refold collisions retain the minimum source round.
Unknown edges use the number of rounds as fallback. The canonical order
resolves ties. `reduceWithOrder` uses at most thirty-one spaces; public
`orderedSpace` accepts an arbitrary supplied list.

`SourceCurrentReductionBirthOrder` proves first observed births, exact minima
after observed refold mappings, injective key-renaming lookup, and fallback
bounds. It also bounds a supplied total reduction step to thirty-one spaces.
The component accepts an empty observed history as an empty table. The actual
source rejects an empty history. Actual reduction-step completion and
nonempty history entry remain separate source obligations. Arbitrary public
histories also need an Int counter bound and Double ordering correspondence.

Earlier synthesis statements that use identity weights retain their old
source scope. Current round ordering needs traversal, immutable identity,
refold-edge mapping, min-table, Double, and canonical sorting correspondence.
Passing the new history-order regression does not prove the general claim.

## Validation and outstanding local source changes

The strict Nix build of all components, tests, and benchmarks passes.
All six suites pass: 321 core, 226 generator, 167 refinement, 34 GHC-fit,
and 22 decision-model examples, plus golden. Fourmolu checks ten changed
Haskell files. Cabal-gild checks all four active packages. No local test file
is changed.

The package delta from main contains only the historical constructor-repair
changelog entry and the equality caller comment that names
`lean/repro/OuterCallerCycle.hs`. There is no outstanding local executable
Haskell patch at this checkpoint. `FINDINGS.md` now records current repair
status for external work. Add every later Haskell fix there with the failure,
file, commit, validation, and upstream status.
