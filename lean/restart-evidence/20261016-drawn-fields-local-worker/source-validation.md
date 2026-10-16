# Drawn fields and recursive field-pool repair validation

Checked 2026-10-16 13:52 CEST. Merge source HEAD: `896b0a1cb36c58531ee24c5b4edfff0e935111c6`. Incoming main: `c0cc8a05` (PR64 drawn typing fields and PR65 FieldAtomOnDatatype repair). Previous main: `5399d310`.

All requested validation passes. The incoming delta changes seven generator paths, including six Haskell files. Their recorded hashes match before and after validation. The preserved historical Chain reproducer also retains its exact bytes. This owner made no source, older evidence, proof, Git, Audit, or root-document edit. All actual process handles reached terminal exit 0. The sole Haskell build slot was explicitly released to root at 13:51 CEST. No owned process remains.

## Strict all-component build

```sh
nix-shell --run 'export PATH=/usr/bin:$PATH; cabal v2-build all --enable-tests --enable-benchmarks --ghc-options=-Werror -j1'
```

Terminal exit 0, handle 68327. Raw log: `source-strict-build.log`. Libraries, sublibraries, executables, tests, and benchmarks build. Only the previously observed dynamic-symbol type/size linker warning for `IsStringSymbol_closure` remains. No hoogleplus installed-unit recovery was needed.

## Six suites and golden

```sh
nix-shell --run 'export PATH=/usr/bin:$PATH; cabal test cfta:unit-tests cfta-generator:gen-tests cfta-generator:refinement-tests cfta-ghc:ghc-fits-tests cfta-ghc:hole-fits-golden decision-model:decision-model-test -j1 --test-show-details=direct'
```

Terminal exit 0, handle 35230. Raw log: `source-tests.log`. Current totals are **798 examples, zero failures, plus the hole-fit golden suite**:

| Suite | Result |
| --- | --- |
| cfta unit-tests | 321 examples, 0 failures |
| cfta-generator gen-tests | 240 examples, 0 failures |
| cfta-generator refinement-tests | 180 examples, 0 failures |
| cfta-ghc ghc-fits-tests | 35 examples, 0 failures |
| decision-model decision-model-test | 22 examples, 0 failures |
| cfta-ghc hole-fits-golden | PASS |

The four new drawn-field regressions pass: symbolic million-value counting, finite-pool language agreement, invariant filtering and count agreement, and DrawnField rejection by the plain builder. The new direct recursive-field regression passes with FieldAtomOnDatatype. These are current counts; the older 793-example result is not attributed to this source.

## Formatting and metadata

```sh
nix-shell --run 'export PATH=/usr/bin:$PATH; python3 lean/restart-evidence/20261016-drawn-fields-local-worker/source-format-metadata.py'
```

Terminal exit 0. Fourmolu check passes on exactly the six incoming Haskell files. Cabal-gild check passes on all four active package files. `cabal check` passes in `cfta`, `cfta-generator`, `cfta-ghc`, and `decision-model`. Exact commands, working directories, log names, and exit codes are in `source-format-metadata.json`. No formatter writes source.

## Preserved Chain reproduction

```sh
nix-shell --run 'export PATH=/usr/bin:$PATH; cabal exec -- runghc -package=cfta -package=cfta-generator lean/restart-evidence/20261016-frontend-node-view-refresh/derive-self-field-draft.hs'
```

Terminal exit 0, handle 60585. The unchanged historical script SHA256 is `aca168328f288fedf671fc30a535bf5d4643aeaed1662f3bd214936f663ee8ac`. No historical script, log, or note is edited. Its old draft comment remains historical artifact text. New output is saved only in `source-derive-self-field.log`:

```text
(field holds, type-wide holds, independent all-node invariant):
(True,True,False)
High-level field-local derivation status:
Left (FieldAtomOnDatatype "Next" 0)
High-level type-wide replacement status:
Left (UnknownConstructors ["End","Next"] [])
Field-local generated values and independent validity:
FieldAtomOnDatatype "Next" 0

```

The public derivation now rejects this direct self-type field pool with `FieldAtomOnDatatype "Next" 0`. It no longer returns a generator containing `Next (End False)`. The standalone `holds` values remain `(True,True,False)`. Thus the repair restricts accepted derivation inputs; it does not make `holds` recursively validate an opaque pool. This is a repair-domain statement, not a new defect report or a theorem for arbitrary helper pools. The type-wide replacement still returns its earlier UnknownConstructors error.

`source-validation-inputs.json` records all initial source and reproducer hashes and exact build/test/repro commands. `source-validation-results.json` records all terminal handles, actual counts, explicit after hashes, and unchanged-source checks. The source feature and error remain separate frontend proof obligations. Passing these checks does not prove rank equivalence between typingLTA and fromTypingRules, a new Lean adapter, or whole-library correspondence. No additional behavior repair is required by these checks.
