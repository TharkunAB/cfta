# Upstream main refresh at 239feb64

Merge `b3d06a08` retains formalization parent `0c9afd41` and upstream
`239feb6477ecf352c696ed4d63a450fb4008e1ac`. The merge does not rewrite history.
The local backup is `backup/formalize-before-main-239feb64-20261015-1154`.
The starting snapshot is `/tmp/mcfta-main-refresh-start-20261015-1153/`.
Its SHA-256 manifest contains 2,514 files. It also retains both unverified
intersection drafts and their limit record.

## Source comparison

Core and generator source files and tests are unchanged from `0c9afd41`.
All 2,314 files in the Lean tree are byte-identical before these documentation
updates. Existing proofs, counterexamples, retained reproductions, marked
drafts, stashes, and other worktrees remain intact. The optimized interned
core, older constructor and equality work, and the Sized contracts retain
their definitions. Exact size classes, finite execution, size order, and
the two distinct rank inverse contracts remain separate obligations.

Upstream adds `decision-model` to `cabal.project`. It provides questions,
option scores, chunking, two-order scoring, ranking, and HTTP clients for
Ollama and compatible chat servers. These modules have no formal source
model or verified extraction. Their tests are execution evidence only.

Upstream moves `Data.CFTA.GHC.Session` from `cfta-ghc/common` to the library
at `cfta-ghc/src`. It adds session options and expression compilation.
GHC session behavior and these new exports remain outside formal coverage.
The application and benchmark now use the library module. License metadata
and CI also change. No core proof adaptation is required by this source diff.

## Validation

All Haskell commands run in `nix-shell` with `/usr/bin` first in PATH.
This uses the system linker for libgmp.

- `cabal v2-build all --enable-tests --enable-benchmarks --ghc-options=-Werror`
  passes, including the new package and the moved session library.
- `cabal v2-test all --ghc-options=-Werror --test-show-details=direct`
  passes all six suites: 293 core, 147 refinement, 210 generator, 15 GHC-fit,
  and 22 decision-model examples, plus the hole-fit golden suite.
- Fourmolu passes for changed Haskell files. Cabal-gild and `cabal check`
  pass for all four packages.
- The pinned Lean 4.34.1 aggregate build passes 1,890 jobs and checks
  dependencies of 48,594 theorems. Only `propext`, `Classical.choice`, and
  `Quot.sound` occur. The older unused `inputs` warning remains.

Logs are `/tmp/mcfta-main-refresh-{build,tests,format,metadata,audit}-20261015.log`.
These checks do not establish whole-library correspondence or termination.

## Next proof target

Continue [the caller boundary investigation](notes-origin-boundaries.md).
Derive a decreasing rank or finite dependency argument for actual constrained
outer child continuations. Include native narrowing, physical combination
and descent, Mu cleanup, and stopping at Mu and union inputs. Equality-free
ordinary regions already complete for every inherited payload. Do not assume
a future finite node inventory, completed caller graph, or successful receipt
to prove general existence. General caller termination, the outer memo table,
open contexts, repeated fixed points, getAllAtPath, native containers, GHC
scheduling, the new decision-model modules, and extraction remain open.
