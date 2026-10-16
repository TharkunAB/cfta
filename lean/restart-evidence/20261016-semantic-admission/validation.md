# Semantic admission checkpoint validation

Source main is `8f85ddb605327bd088aae970ab058137c4f6d762`.
The starting formalize checkpoint is `f37a8fe5bfd794693bcdc1c10a3a59b288421119`.
The opening `git pull --ff-only` completed with no changes.
New proof commits are `953f3b1a`, `61ce6cff`, and `048d9fce`.
No Haskell implementation or test files change in this checkpoint.

## Canonical Lean validation

Use the pinned Lean 4.34.1 toolchain and the repository `lean` directory.
The final `lake build MicroCFTA.Audit` finishes with exit code zero.
It passes 2311 jobs and checks dependencies of 56189 theorems.
The allowed foundations are `propext`, `Classical.choice`, and `Quot.sound`.
Only the old unused-input warning occurs in the full build.
The terminal build log is `audit.log`.

Focused builds also pass for all six additive modules. Their local job
counts describe their dependency targets, not the number of new theorems.

| Module | Public axiom reports | Full signatures | Kernel examples |
| --- | ---: | ---: | ---: |
| InputModelTransport | 14 | 14 | 4 |
| InputGrowthModels | 6 | 6 | 3 |
| GrownInventory | 8 | 8 | 11 |
| ContextRebase | 23 | 23 | 5 |
| AdmittedQuery | 2 | 2 | 3 |
| AllocatedClassEntry | 4 | 4 | 8 |
| Total | 57 | 57 | 34 |

The probes check the complete public types and the actual grown-inventory,
same-state cache, generated-root, and next-query compositions. The query
integration derives actual `execute.done`, closed output, exact physical
intersection language, residency, Original syntax, final fields, Scoped,
and Idle. It supplies no target model law. Old contextual cache laws,
returned-request admission, and seen-pair admission remain explicit.
Separate review files found no material defect.

Saved failed build and probe logs remain. The first admitted-query build
failed because the empty-list membership disjunction was not simplified.
The final source and final build correct it. The first preservation report
used module names as paths for one older manifest. The verifier now expands
those names to their actual source paths. The saved first report is not a
source-loss report. All final frozen checks pass.

## Haskell validation and external handoff

`git diff --exit-code f37a8fe5 -- cfta cfta-generator cfta-ghc decision-model`
passes with no output. Reuse the unchanged-source strict Nix all-component
build, 777 examples plus golden, five-file Fourmolu, and four-package
Cabal-gild results from the source refresh.

The diff against current source main contains only the retained historical
fresh-probe changelog entry and the equality-endpoint reproducer comment.
It contains no outstanding behavior patch. The complete repair registry
remains at the top of root FINDINGS.md. Each later Haskell fix must record
its failure case, affected files, commit, checks, and upstream status there.

## Preservation

`verify-preservation.py` checks all 3463 starting files. No file is missing.
All 2304 older non-Audit Lean sources retain identical bytes. The only
changed baseline files are the seven restart documents and additive Audit
imports. All ten preceding frozen manifests and the current six-module
manifest pass. Stashes, other worktree records, and the root Haskell registry
remain unchanged. `frozen-modules.json` records the six source hashes.
`preservation-final.json` contains the complete check result.

Earlier external draft bytes were unavailable before this checkpoint.
No recovery or reverification of those bytes is claimed.

Scoped source and documentation `git diff --check` passes. Saved raw logs
can contain whitespace from Lean output and failed diagnostic contexts.

## Remaining proof obligations

The new query theorem establishes one next query after actual inventory
growth. It does not derive old admission from conditional cache laws.
It also does not derive admission of all newly returned internal requests.
That causal invariant is needed to iterate generated-query histories.

The allocated current Scan theorem establishes finite physical completion
at the actual precheck state. Common-subtree inclusion, the checked class
witness, stopped-class rejection soundness, the complete constrained outer
caller, and all other full-library boundaries remain active.
Read `lean/notes-current-native-semantic-admission.md` for the precise scope.
