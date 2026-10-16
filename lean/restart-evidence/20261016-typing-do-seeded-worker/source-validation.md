# Qualified typing do Haskell validation

Checked 2026-10-16 13:22 CEST on Linux. Source merge HEAD: `82d47236a7f4768f2555f1547af73191f8d6159f`. Incoming main: `5399d310` (PR63). Previous main: `999c04a5`.

All required validation passes. The delta has five generator paths, including three Haskell files. All five initial source hashes remain unchanged after validation. This owner made no Haskell, earlier proof, Git, Audit, or documentation edit. The single Haskell slot was explicitly released to root after both build and test handles terminated. No owned process remains.

## Strict all-component build

```sh
nix-shell --run 'export PATH=/usr/bin:$PATH; cabal v2-build all --enable-tests --enable-benchmarks --ghc-options=-Werror -j1'
```

Terminal exit 0, handle 88176. Raw log: `source-strict-build.log`. Libraries, sublibraries, executables, tests, and benchmarks build. The existing dynamic-symbol type/size linker warning for `IsStringSymbol_closure` remains. It causes no build failure. The hoogleplus installed-unit recovery was not needed.

## Six suites and golden

```sh
nix-shell --run 'export PATH=/usr/bin:$PATH; cabal test cfta:unit-tests cfta-generator:gen-tests cfta-generator:refinement-tests cfta-ghc:ghc-fits-tests cfta-ghc:hole-fits-golden decision-model:decision-model-test -j1 --test-show-details=direct'
```

Terminal exit 0, handle 22427. Raw log: `source-tests.log`. Current totals are **793 examples, zero failures, plus the hole-fit golden suite**:

| Suite | Result |
| --- | --- |
| cfta unit-tests | 321 examples, 0 failures |
| cfta-generator gen-tests | 240 examples, 0 failures |
| cfta-generator refinement-tests | 175 examples, 0 failures |
| cfta-ghc ghc-fits-tests | 35 examples, 0 failures |
| decision-model decision-model-test | 22 examples, 0 failures |
| cfta-ghc hole-fits-golden | PASS |

These counts come from this run. The preceding 791-example result is historical for this source. Both new do-notation regressions pass: ordered language agreement with the explicit rule list, and dependent choices with guard filtering over 35 fractions.

## Format and package metadata

```sh
nix-shell --run 'export PATH=/usr/bin:$PATH; python3 lean/restart-evidence/20261016-typing-do-seeded-worker/source-format-metadata.py'
```

Terminal exit 0. The script records exact commands, working directories, log names, and exit codes in `source-format-metadata.json`. Fourmolu check passes on exactly the three changed Haskell files. Cabal-gild check passes on all four active package files. `cabal check` passes in `cfta`, `cfta-generator`, `cfta-ghc`, and `decision-model`. All checks run in Nix with `/usr/bin` first in PATH. No formatter writes source.

`source-validation-inputs.json` records the initial source hashes and complete build/test commands. `source-validation-results.json` records terminal results and counts. The raw build, test, format, and package logs remain here. `source-do-review.md` records the literal list semantics, ordering, pattern-failure behavior, and unproved frontend/runtime boundaries. No Haskell defect or required fix was found. This validation does not establish a new Lean adapter or whole-library source correspondence theorem.
