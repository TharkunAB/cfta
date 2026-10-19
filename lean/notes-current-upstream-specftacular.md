# Upstream Specftacular import

Updated: 2026-10-19 12:07 CEST. Main: `b45051e3e772c8e0343215b6d7dd703995fa300a`.
Merge: `fec741514650ab0e6f5bc125e89967811c8e1b90`. Prior checkpoint: `60403eced`.

PR #66 adds the `specftacular` and `specftacular-ghc` packages to the Cabal
workspace. It adds 48 files, including 25 Haskell files. The five existing
changed paths are CI, the root README, cabal.project, cfta-ghc/README.md
and scripts/release.sh. The README merge retains the local proof links.
All 242 earlier Haskell files and all earlier proof and evidence files
retain their bytes. The optimized cfta core is unchanged.

The main package exposes Specftacular, DecisionTree, Rewriting, Types and
Utils. It discovers candidate equations with cfta term search, randomized
evaluation and rewriting. The GHC adapter exposes session-based signatures
and compiles expressions and QuickCheck generators. These packages target
GHC 9.14.1.

These interfaces have no Lean specification or refinement proof in this
checkout. Their stochastic validation, discovered-law soundness contract,
rewrite behavior, term/type conversions, search phases and GHC adapter are
additional coverage obligations. A candidate that passes finitely many
random tests is not a universally valid equation. The upstream README
explicitly records false candidate laws with too few tests. This refresh
does not establish a new Haskell bug or request a repair.

The core cfta proof target remains unchanged. Fresh modeled construction
completion and the conditional root-language guarantee remain proved.
General outer completion, repeated-pass convergence and Haskell runtime
refinement remain open. The new application and adapter are separate
unproved coverage. Do not infer their correctness from the cfta theorems.

The merge preserves prior local work and adds no manual Haskell patch.
Only source integration and byte preservation were checked here. No new
Haskell build, test or benchmark result is claimed. The exact upstream
paths and hashes are in restart-evidence/20261019-recursive-event-observation/
upstream-refresh.json. Publication still awaits direct approval.
