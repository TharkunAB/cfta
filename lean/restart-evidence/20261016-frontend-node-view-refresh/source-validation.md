# Merged frontend Haskell validation

Checked 2026-10-16 13:09 CEST on Linux. Source merge: `9aaffc9574cc63adba23ed168e0aa768f033f0a7`, incoming main `999c04a5`, previous main `ccebf0f7`.

All required validation passes. The delta has nine generator paths, including seven Haskell files. The recorded nine source hashes remain unchanged after validation. This owner made no Haskell, earlier proof, Git, Audit, or documentation edit. The single Haskell build slot was released to root after the test process terminated. No owned process remains.

## Strict all-component build

```sh
nix-shell --run 'export PATH=/usr/bin:$PATH; cabal v2-build all --enable-tests --enable-benchmarks --ghc-options=-Werror -j1'
```

Terminal exit 0. Raw log: `source-strict-build.log`. Libraries, sublibraries, executables, tests, and benchmarks build. The existing dynamic-symbol type/size linker warning for `IsStringSymbol_closure` remains. It causes no build failure. The installed hoogleplus recovery was not needed.

## Six suites and golden

```sh
nix-shell --run 'export PATH=/usr/bin:$PATH; cabal test cfta:unit-tests cfta-generator:gen-tests cfta-generator:refinement-tests cfta-ghc:ghc-fits-tests cfta-ghc:hole-fits-golden decision-model:decision-model-test -j1 --test-show-details=direct'
```

Terminal exit 0. Raw log: `source-tests.log`. Current totals are **791 examples, zero failures, plus the hole-fit golden suite**:

| Suite | Result |
| --- | --- |
| cfta unit-tests | 321 examples, 0 failures |
| cfta-generator gen-tests | 238 examples, 0 failures |
| cfta-generator refinement-tests | 175 examples, 0 failures |
| cfta-ghc ghc-fits-tests | 35 examples, 0 failures |
| decision-model decision-model-test | 22 examples, 0 failures |
| cfta-ghc hole-fits-golden | PASS |

These counts come from this run. The older 788-example result is not used.

## Format and package metadata

```sh
nix-shell --run 'export PATH=/usr/bin:$PATH; python3 lean/restart-evidence/20261016-frontend-node-view-refresh/source-format-metadata.py'
```

Terminal exit 0. The script records exact commands, working directories, log names, and exit codes in `source-format-metadata.json`. Fourmolu check passes on exactly the seven changed Haskell files. Cabal-gild check passes on the four active package files. `cabal check` passes in `cfta`, `cfta-generator`, `cfta-ghc`, and `decision-model`. All checks run in Nix with `/usr/bin` first in PATH. No formatter writes source.

`source-validation-inputs.json` records the initial source hashes and complete build/test commands. `source-validation-results.json` records terminal results and counts. The raw format and package logs remain here. No Haskell fix is required by these checks. A separate focused source-semantic reproduction, if run by root, is outside this validation result. Passing these checks is not an end-to-end formal correspondence theorem.
