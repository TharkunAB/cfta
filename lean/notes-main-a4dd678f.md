# Main a4dd678f: state synthesis and bounded normal-form work

Source main `a4dd678fac265133fd782208d4845bdcae1228ff` is merged at
`1a421c7de5f882b92da6eac29f96cbdef91dbd8c`. The merge changes 13 files.
It adds generator States, its host test, and GHC States. It changes Walk,
Fits, NormalForm, package lists, changelogs, a benchmark, and existing tests.
The equality, Sized, import, and interned production bodies are unchanged.
The previous local equality repair retains its bytes.

## New source behavior

`Gen.Synthesis.States` builds states from a host goal key, a size, and the
required argument indexes. Refinements are cached by key and child count.
States are cached by key and budget after complete builds. Child budgets
partition the remaining size and argument uses. The search can walk the
table in preorder or use one interned automaton per size. The automaton
removes the first-argument exclusion rules before counting and listing.
The host checker still checks complete programs and retains dead prefixes.

`GHC.States` supplies goal keys and refinements from GHC. Child goals include
the parent's instantiation but omit sibling unifications and the parent's
wanteds. The table is an over-approximation. Whole-program checking is
required. The adapter filters leaves by result heads and excludes unused
unconstrained result variables unless the program must use them.

Walk now reports Solved, Exhausted, or OutOfTime. Its caller supplies hookNew
and retains fit deduplication. Fits selects Hectare or States mode, keeps
shared fit reporting, and reports state figures. Existing earlier Walk
models retain their historical hook and reporting scope. Full current
host, hookNew, deadline, and mode dispatch correspondence remains open.

## Checked source components

`SourceSynthesisStateBudgets` ports the positive compositions, signed argument
assignment order, and retained-split filter on nonnegative sizes. The actual
composition loop contains exactly the positive lists with the requested
sum and length. Argument assignment retains one list per child. The filter
retains exactly its feasible original occurrences. Rejected and retained
counts account for every original occurrence. Each retained split has the
requested child count and preserves the entire remaining size. Every child
has positive size strictly below the parent's root-inclusive size.
The proof retains the source order and signed argument indexes. It does
not prove complete argument-partition semantics, host refinement validity,
whole cached state builds, automaton conversion, pruning, or whole search.
Negative size/count calls and machine conversions are outside this natural
size port. Source callers provide the intended nonnegative domain.

`SourceNormalFormBudget` ports the ordered quotation work scheduler. Every
job spends before it requests a value view. Beta markers and quoted nodes
share the same remaining budget of 1,000,000. Case jobs retain scrutinee,
explicit alternative, and default expansion order and depths. Accounting,
sequential composition without a budget reset, successful extra-budget
stability, and rejection of an endless beta-marker loop are proved.
The separate finite output-shape check accepts exactly at most 20,000 nodes.

The view supplier is a total mathematical function. Deriving each outer
value view and applied closure observation from the actual source evaluator
remains open. The work scheduler does not construct the final NormalForm.
Pair and identity-case contraction readback, full Core translation,
nonnegative metadata, machine conversions, and contextual equality remain
open. These are not whole-normalizer termination or GHC equivalence proofs.

## Changed interface inventory

| Source module | Current role and proof boundary |
| --- | --- |
| `Gen.Synthesis.States` | New `Budget`, `Goals`, `Refinement`, `Walking`, `EdgeOrder`, `Figures`, `emptyFigures`, `searchStates`, `searchStatesWith`, and `budgetSplits`. The budget component is checked. Host refinement, cached state construction, automaton exclusion/listing/counting, and complete search correspondence remain. |
| `Gen.Synthesis.Walk` | New `Outcome` and `progressOutcome`; `Hooks` adds `hookNew`. Dead-prefix operations and `timed` are exported for States. Earlier token/marker models remain components. Caller deduplication, complete new outcome/stop behavior, deadlines, and runtime need current bridges. |
| `GHC.States` | New `holeGoals` supplies host keys and refinements. Result-head indexing, leaf filtering, GHC snapshots, restore, and checker adequacy remain. |
| `GHC.Fits` | New `Mode`, `Options.optionMode`, and `Statistics.statisticsStates`. Current mode dispatch and shared reporting use both proposal sources. Earlier marker, deduplication, and normal-form models retain their stated component scopes. Full current host wiring remains. |
| `GHC.NormalForm` | Delayed `VStep`, shared spend, ordered quotation, and a separate size gate. The new scheduler and finite shape contracts are checked. Evaluator/closure exposure and final contraction readback remain. |

## Source validation

The required strict Nix build passes all libraries, executables, tests, and
benchmarks with `-Werror`. All six suites pass 743 examples plus the golden
check. Fourmolu passes all nine changed Haskell files. Cabal-gild passes all
four active packages. No additional Haskell change is made for these proofs.
Logs and exact commands are in `mcfta-class-language-haskell-validation-20261016.json`
in the checkpoint snapshot. These checks do not prove source correspondence.
