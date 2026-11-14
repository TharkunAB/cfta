# Checked identity prefix laws

The checked code commit is `4b06f71783c6824be49aed08534d0353a2710242`.
The remote `formalize` ref was independently checked at that commit.
The baseline is `a68a1efcb6f23a1dd765bd72728babdb372b9e3a`.
Six public proof modules were added. All old files other than Audit retain their bytes.
Audit adds imports and explicit reports. Its old bytes remain intact.

The results use the existing narrowing backend and receipt types:

| Module suffix | Checked result |
| --- | --- |
| `IdentityPrefix` | Identity preparation and exact pending-prefix behavior retain the same read, value, heap, queries and literal caller advance. |
| `IdentityCompletion` | A selected pending expansion derives its read/check observations and one common sufficient bound from the existing readiness and index invariants. |
| `IdentityPrefixMetadataErasure` | The exact selected-prefix result agrees after metadata erasure when narrowing is identity, stop is absent and order ignores metadata. |
| `InitialIdentityPrefix` | One accepted current raw-source initializer supplies the existing receipts, exact initial decision and computed identity-prefix behavior. |
| `InitialPrefixFuel` | The initial root read/check agree at every positive fuel, for arbitrary narrowing and without an invariant premise. |
| `InitialIdentityPrefixStable` | The same initializer receipts and prefix behavior hold at every positive common read/check budget. |

The initial decision can be `done` at a recursive boundary. The initializer
theorems retain that decision. They compute prefix behavior and do not execute
the recursive eager worker. The public source startup is raw. The preprocessed
default entry and compiled Haskell correspondence remain open.

The central missing result remains one finite accepted term of the same original
root, with one consistent assignment that completes the same emitted partial
root. The whole-worker metadata-erasure theorem and current-source universe
ownership theorem remain unproved. The included plans and projection draft are
explicitly uncompiled. Keep every other obligation in HANDOFF.md.

## Reproduce the checked code

Check out the checked code commit in a separate checkout. Run:

```sh
nix-shell shell.nix --run 'cd lean && lake build MicroCFTA.Audit'
nix-shell shell.nix --run 'cd lean && lake env lean -j1 -DwarningAsError=true MicroCFTA/Audit.lean'
```

The latest full check audits axiom dependencies for 95,308 imported project
theorems. Audit has 4,919 direct imports: 4,918 project imports and Lean.
The 30 explicit axiom reports are a separate count. Only `propext`,
`Classical.choice` and `Quot.sound` occur. There are 5,921 project source files.
That count does not assert a separate strict check of every source file.
The three known totality modules outside Audit retain their prior checked
result. Their dependencies did not change in this additive checkpoint.

All publication runs build and strictly check the new module, check an
independent import, then build and strictly check Audit. They run serially in
Nix with one Lean thread, 4 GiB memory.max/high and swap0. The final run is
`runs/mcfta-source-initial-prefix-common-fuel-publication-20261114-0617`.
Its `checked.json` records the actual result.

## Retained history

The packet contains source, scripts, patches, source pins and small logs.
The proof source in Git is sufficient to reproduce the checked claims.
The logs preserve what ran, including failed drafts and their repairs.
They contain no compiled archive. Build outputs can be regenerated.

Historical scripts retain their executed paths. Use each run's source pins
and source copies when reconstructing it. Adapt paths in a separate driver.
Keep the archived driver unchanged. The publication code commits appear in
`status.json` in run order. Text, JSON and patch payloads may use gzip.
`archived-inputs.json` maps each original input to its archived bytes.

The first initializer drafts fail parsing or local proof checks. The third
private check and public run pass. The first positive-fuel draft fails `rfl`.
The second lacks local state type annotations. The third private check and
public run pass. The first positive-fuel publication preparation refers to an
absent `lakefile.lean`; Lean was not dispatched. The metadata pin was repaired
to use `lakefile.toml` before the successful run. No failed run receives proof
credit. Each repair retains its original theorem statement.

`current-source-manifest.json.gz` lists the current source hashes. Its digest
uses sorted UTF-8 lines of relative path, NUL, lowercase SHA-256, and newline.
`current-source-status.json` records that digest. Compare only the same digest
method. `checked-code.patch.gz` reproduces the six-module change from the
baseline. No Haskell, Cabal or test source changed. No new Haskell fix was
established. Record future Haskell fixes in FINDINGS.md.

The later current-source syntax port and eight CPS transport bodies are frozen
uncompiled drafts. Their replay checks establish bytes, not Lean validity.
The projection check first failed its pin-schema preflight before Lean ran.
Check2 used the same expected digests in the correct schema, then failed the
scan and receipt proof steps. The failed file receives no proof credit.
The current-source port adds a bridge to the historical table proof. That patch
has not been applied to the checked code. Its first-occurrence ownership proof
remains open. These later drafts do not change the six checked public results.

The later repaired five-map transport file passes private check3. Its five
reports include two axiom-free proofs. This is private component progress.
The CPS check first failed import-path setup. Check2 uses temporary symlinks
to existing import objects. The maps object passes; the CPS file fails proof
checks. The packet excludes every temporary object and symlink overlay. No
whole-worker claim follows from either the draft or the failed CPS check.
