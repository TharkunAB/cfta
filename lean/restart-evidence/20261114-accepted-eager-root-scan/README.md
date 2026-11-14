# Accepted eager producer and original root scan

Proof commit: `bbb03345da4197750ebc14d27d9553ec46a1951c`.
Previous checkpoint: `3f3777d157a4294eb2c11be07fb992d6731953cf`.

`SourceSynthesisCurrentAcceptedEagerRootScanOrigin` exports
`SourceSynthesisCurrentProgramEagerOutputs.accepted_initial_root_scan_origin`.
It calls the existing accepted producer once. It retains the same initializer,
build, cache, handle, bound, returned outcome and full resource/readback receipt.
For every larger fuel bound, that same outcome retains its initial prepared
eager scan and indexed original-source row provenance. The global stop rule is
`none`. Depth zero and unsupported observations have no invented active scan.
The result does not construct a joint finite assignment or prove finite typing.

The old 139-line receipt remains intact inside the new statement. The added
clause had two copied identifier errors: `width` instead of `bits + 2`, and
unbound `whole` instead of `expression`. The latter introduced an unintended
implicit parameter. The exact corrections and inverses remain recorded.
The corrected private header has 231 lines and SHA256
`351d3a27f7dd550ae0122da0401b6c9bd6c57f8e999c73498eb011be7985e820`.
The implementation sets `autoImplicit false`. No equality or model premise was
added to replace either error.

Checks 3 through 9 failed. Check 10 passed on the 367-line private input.
The public module has 376 lines. The final repairs reduce the same decision,
prefix, preparation, indexed scan, row, head, suffix and own-preparation results.
They normalize the same predecessor-plus-one expression and reconstruct the
same source witnesses. Failed elaboration and recovery have no proof credit.

The public strict check, independent import, Audit build and strict Audit passed.
The working tree contains 5915 MicroCFTA source files. Audit has 4913 direct
imports. Its environment passed axiom dependency checks for 95130 theorems. These
counts measure different things. An Audit pass does not check every standalone
file. Three affected totality modules outside its import closure passed separate
baseline build, strict source and standard-axiom import checks before factoring.
All 5913 earlier non-Audit source files retain their exact bytes.

The final source-tree SHA256 is
`5eba6b7f39a7ea74d471f6577388787d4ea3ea35531d830c9e1dce5aab3135ad`.
The new public law uses only `propext`, `Classical.choice` and `Quot.sound`.
Checks ran in the project Nix shell with one Lean thread, memory.max and
memory.high of 4 GiB, and no swap.

`manifest.json` records external bases, exact source deltas, compiler inputs,
failed outputs, final reports, source reviews and external-state records.
It references existing objects in the preceding packet instead of copying them.
`independent-replay.json` records a separate replay of all 23 GNU patches with
`--batch --fuzz=0`. No patch used an offset or fuzz. Every result matched its hash.
No build archive or compiled object is stored.

To repeat the final check, use a checkout of the proof commit. Copy the recorded
`publication/check-final.py` object to an empty temporary directory as
`check-final.py`. From the repository root, run `restore-inputs.py` with that
directory as its argument. It reconstructs and checks the exact baseline pins.
Then run the driver through the documented `heavy-management/bin/capped`
command with `--mem 4G --time 15m`. The driver writes its final source-pin list.
The full historical pin lists are reconstructible from Git and are not copied.

The independent narrowing review validates source inverses and old interfaces.
It supplies no new operation proof. The saved required-path audit establishes
a coverage obstruction: the Required forest has a PrefixShape receipt, while
the worker retains the original intersection query. Fresh opaque allocation
and recurrence parking also require their original path buckets in a completion
proof. Closedness and Type routes do not establish path existence.

The external Liquid duplicate-name fix is in open, unmerged PR
[#212](https://github.com/TharkunAB/cfta/pull/212), head
`438be86d6cc3642a44a25816733ad922a5ee6e99`. Its source and tests belong to that
external change. This checkpoint changes no repository Haskell or Cabal file.

The full goal remains active. Joint finite completion, default preprocessing
and hook correspondence, depth completeness, exact size contracts, counting,
weights, training, both rank/unrank inverses, host bounds and compiled Haskell
correspondence remain required.
