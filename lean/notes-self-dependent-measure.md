# Self-dependent measure extraction counterexample

The public `refinedNodeByRoots` route explicitly rejects roots that contain
open integer names. Its documentation says that children from `every` give
`IntegerLeafRead`. The implementation performs that prefix check before it
calls the user's refinement function.

A different public route reaches a self-dependent symbolic measure without
constructing a reserved name. Define a closed leaf with refinement
`\v -> v .== v`. Pair it with an integer from `every`, bounded to zero or one.
Use `measuredNode` with addition as its measure. The first child extractor
returns the refined value variable itself. The result refinement becomes
`v == v + x`, where `x` is the compiler's coordinate for the integer sibling.

Before the repair, the temporary probe `/tmp/microcfta-self-measure.hs` placed either
`Satisfies [0] Bottom` or `Holds [[0]] Bottom` above that measured child.
For both guards, the complete `validOutcomes` result was `Right [(0,1)]`.
The symbolic compiler instead returned a generator whose `values` and `pmf`
were `Left EmptyGenerator`. Replacing `every` with `elements [0,1]` gave the
compiled member `(0,1)` with probability one. The bare symbolic measured
child also compiled successfully with both `(0,0)` and `(0,1)`.
The log is `/tmp/microcfta-self-measure.log`.

At sibling value one, the child refinement `v == v + 1` is inconsistent.
Mathematical entailment therefore proves Bottom from it. The open parent
translation substitutes into Bottom and obtains Bottom, which removes both
points. This shows why the parent formula proof cannot assume target
satisfiability merely from successful syntactic extraction.

The source `measured` documentation requires each referenced child to have
an exact measure. It promises `InexactMeasure` when a child has no measure.
The self-equality leaf fails that requirement. Thus the supported repair is
to report the promised error, rather than silently accept that child and
produce different languages on the open and listed paths.

`definingTerm` itself is a public syntactic extractor. Its documentation does
not promise an occurs check. The repair retains that API and rejects
extracted measure terms that mention `valueName` at the measure construction
and parent translation call sites. Both callers test the source `freeNames`
of `term .== 0`. The singleton `onlyPoint` branch retains priority.
At measure construction, an omitted used child
replacement leaves its positional formal and produces `InexactMeasure`.
At parent translation, unavailable extraction produces `IntegerLeafRead`.

The retained probe is `repro/SelfDependentMeasure.hs`. It uses only public
generator and refinement APIs and inserts no reserved integer name. It
checks both parent guard forms on open and listed integer children. Both
the compiler and `validOutcomes` now return `InexactMeasure "m"`. Independent
measures retain their values. An exact singleton refinement with a syntactic
self-reference still works because `onlyPoint` has priority.

`DefiningTerm.termOf_exact` proves that every accepted extraction defines
exactly one integer in every ambient environment. It derives existence and
uniqueness without a satisfiability premise. `ParentGuardFormula` uses this
result to derive exact target values and mathematical parent guard meaning.
The proof does not identify arbitrary solver verdicts with mathematical truth.

Validation used the required Nix shell. The focused measure tests and the
retained probe pass. All three suites pass: 282 core tests, 194 generator
tests, and 141 refinement tests (617 total). Fourmolu, both affected package
files' cabal-gild checks, and `git diff --check` pass. The two unrelated ECTA
package files have existing cabal-gild differences and remain unchanged.
