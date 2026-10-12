# Source adapter for finite automaton indexes

`SourceFiniteAutomaton.exact_index_api` instantiates the mixed compiler in
`FiniteAutomatonDriver`. It derives the compiler's local semantic laws from
source row structure, source constraint compilation, parsed equality classes,
the compact gate, and the symbolic worker proofs. It does not assume that the
root compiler preserves the language.

The theorem gives these results for each root:

- Compilation terminates at the derived structural execution bound.
- `EmptyGenerator` occurs exactly when the accepted language is empty.
- A successful result has positive cardinality.
- Every integer in `0 .. count - 1` selects one term.
- No other integer selects a term.
- Two successful ranks cannot select the same term.
- Every accepted term has a rank.
- The inverse returns no rank exactly for terms outside the language.
- The inverse and decoder use the same compiled plans.

The guard-support precheck calls `SourceIndicatorCompiler.constraintIndicators`
on the listed reachable rows. Successful compiled row readback proves this
check true. A retained theorem also proves that an unsupported reachable
guard makes the check false. `FiniteAutomatonDriver` retains the public
empty-root-before-unsupported-guard error order.

## Symbolic callback

`SourceFiniteBackend` constructs the callback from
`SourceSymbolicStableIndex.stable_source_index`. This theorem already uses
actual source indicator compilation, complete guard evaluation, graph
operation row readback, and allocation histories.

The callback calls the symbolic `unrank` and `rankOf` workers. It does not
search a list of previous terms. The count agrees with the source cardinality
worker. The construction rejects exactly zero cardinality. `worker_correct`
proves the local total decoder and exact inverse required by the compact
parent. `worker_language` proves the complete independent accepted language.

The finite index list from the stable worker theorem is a proof witness for
the workers' order. It is not a new operational enumeration algorithm. The
proof port replaces unrestricted worker execution with a proved execution
bound. Invalid inverse inputs can require a larger bound than valid members.
`inverseFuel` selects that finite bound for each submitted term. No uniform
bound on all possible invalid input terms is assumed.

## Compact guards and paths

`SourceCompactGuards.positive` models the source `positiveEqualities` syntax
test before equality normalization. It accepts `Top`, distinct-path `Same`,
and conjunctions of those guards. It rejects reflexive `Same`. Such a guard
requires path existence and is a residual in the source.

`positive_exact` proves the extracted classes have the exact current complete
guard semantics. `positive_active` proves all extracted classes are
nontrivial. `normalized_guard` uses the existing completed-normalization
theorem to combine cached equalities and extracted guard equalities. It
derives the complete guard law used by compact indexing.

`arrayNormalize` runs `EqualitySource.normalizeArray` at proved iteration and
work bounds. `arrayNormalize_finished` derives termination from the concrete
parent-array normalization theorem. `positiveNormalized` models the source
normalization at every `Same` and every step of the conjunction right fold.
`combineEqualities` retains contradiction and empty-input shortcuts.
`sourceEqualities` also retains the cached-field shortcut when the extracted
guard has no equalities.

`positiveNormalized_exact` proves the full intermediate normalization
schedule preserves the extracted classes. `positiveNormalized_support`
proves normalization does not change the residual syntax test.
`sourceEqualities_exact` derives the complete current guard law from the
actual source equality pipeline.

`Normalized` is an internal certificate. Its source constructor uses this
proved pipeline. The final `exact_index_api` theorem does not assume this
certificate or assume normalization termination. It requires canonical
cached classes and readback of `sourceEqualities`; then
`source_normalization_readback` constructs the certificate.

The natural-path parser is proved equal to the existing signed source parser
on the represented nonnegative paths. `parse_exact` retains every class and
position in order. `parsed_guard` derives the equality predicate for the
selected child values. `parse_failure` proves that a failed parser under the
no-deep-path gate denotes an empty edge. Thus an out-of-range direct child is
not silently discarded from a nonempty language.

The source edge plan stores only merged groups. It can erase the original
class presentation. `classes` recovers a valid presentation as a proof
witness. `classes_equivalent` proves any recovered presentation enforces the
same original equalities. The witness changes neither group order nor the
actual mixed-radix plan.

## Compact gate and recursive requests

The flag model scans the original row order for shared symbols and overlap.
It scans the ordered rows for residual and deep-path constraints. The
`shared_count` theorem proves the duplicate-symbol test equals the comparison
between distinct symbol count and total row count.

If root labels are distinct, constructor shape proves disjointness. If labels
repeat and the compact gate passes, `AutomatonAmbiguity` proves disjointness
from the actual pair scan. A common child term forces the corresponding
intersection to have a constructor row. The closed-product theorem supplies
the intersection language law. A row permutation transfers disjointness to
the actual compilation order. Edge guards remain part of each language.

`source_semantics` derives every field of `FiniteAutomatonDriver.Semantics`.
No whole-row disjointness, compiled edge law, or symbolic backend correctness
is supplied by the caller.

`source_decrease` uses `closedSourceBudget`. This includes the source closed
self-intersection shortcut and normalized product rows. Allocation histories
derive the topological rank. Each compact group request starts from a child;
its intersection fold cannot increase that child's structural budget. The
proof does not require a finite set of all identities produced during the
compilation.

## Remaining representation boundary

The final theorem still requires these source representation facts:

- `CompiledRows` reads the actual successful indicator output for every row
  in the graph interface, including rows produced by graph operations.
- `ClosedOperationRows` reads product, template, projection, and cleanup rows.
  The associated theorems derive language preservation from this row data.
- `AllocatedRows` records finite constructor allocation histories and issued
  immutable payloads. It derives acyclicity; acyclicity is not a separate
  semantic premise.
- `Rows.permutation` states that sorting retains the original rows. The
  supplied order determines compact rank order. The model accepts the
  supplied source `tied` flag. `CanonicalClasses` separately proves canonical
  class refinement and identity-renaming properties. This adapter does not
  repeat the source sorting implementation or claim order independence for
  different labels with equal user keys. No row-distinctness premise is
  required. The actual gate derives disjoint accepted edge languages,
  including when repeated rows have empty languages.
- `cachedActive` states that the cached equality field contains nontrivial
  canonical classes. `equalityReadback` reads the classes computed by the
  actual staged `sourceEqualities` pipeline. Source array normalization and
  saturation termination are proved by `EqualitySource` and reused here.
  Their low-level mutable-array representation boundary remains the boundary
  documented by those modules. No desired guard-equivalence premise remains.
- The acyclic smart constructor must identify a row-empty node with
  `EmptyNode` for the literal source `(/= EmptyNode)` overlap test. The proof
  uses its constructor-row view. It does not claim that row presence proves
  semantic productivity under arbitrary residual guards.
- Paths in the source guard graph view use natural child positions. The
  parser theorem explicitly covers their signed representation. The separate
  signed-path models cover negative positions. The final source guard graph
  adapter does not instantiate those models here.

Runtime hash-consing, stable identities, mutable cache implementation, and
unrestricted Haskell evaluation remain outside Lean execution. The existing
source worker and cache models provide the mathematical interfaces used
here. These files introduce no new Haskell implementation or external solver
assumption.

## Validation

The focused target is:

```text
lake -d lean build MicroCFTA.SourceFiniteAutomaton
```

The target builds all three new modules and their dependencies. The modules
use kernel-checked proofs. They contain no admitted theorem or native
decision proof. No Cabal build is needed because no Haskell file changes.
