# Actual child-prefix preservation: complete evidence

Source: `087b4d246f40ae07f3fbf30a86bba83d08ecd52d`.
Documentation: `54313dbc42386e5b1b88490690d32b3b019fa528`.
Branch: formalize. The full formalization goal remains active.

Every regular file in the sealed proof area is archived without a filter.
This includes exact compiler inputs and complete raw results, both original
failed candidates and diagnostics, final public readbacks, complete reviews,
source/read-scope records, old and current document bodies, measurements,
Git receipts and the board request with verified readback. Historical source-only
or in-progress labels remain unchanged in frozen reports. Final checked source
identities and outcomes are in final-proof-sources.json and compiler-matrix.json.
Earlier archives remain unchanged.

Payloads: 349. Uncompressed bytes:
40,997,044. Compressed bytes:
8,218,542. SHA-256: `1285335f4e0888d9644154b7ea22e8453a8af6e00740ececb7ced7e478e8de6d`.
Every payload path, byte count and SHA-256 is in manifest.json.

Verify and reconstruct from the repository root:

```sh
python3 lean/restart-evidence/20261028-prepared-child-projection/verify.py lean/restart-evidence/20261028-prepared-child-projection --extract /tmp/mcfta-prepared-child-projection-restored
```

Use a fresh destination. Omit --extract to verify only. The standard-library
verifier checks the compressed file and each payload. It rejects duplicate,
missing, extra, unsafe and non-regular members. It runs no Lean or Haskell code.
Keep reconstructed data immutable. Continue in a new writable area.

Six modules add seven public theorems and no definitions or private helpers.
All six and Audit pass seven exact final strict Lean 4.34.1 checks with
warningAsError and linter.all. Audit passes 4,525 jobs and checks axiom
dependencies of 81,676 theorems. The seventeen-command compiler matrix contains
fifteen passes and two preserved failures. All final checks pass. One query
equality line and two simplifier lines were repaired without contract changes.
All commands measured 4 GiB memory.max/high and zero swap. No proof budget,
custom axiom, native proof evaluation axiom or linter suppression was added.
An unchanged old module retains its old replay warning.

Public: 708 theorem signatures/axiom lists and 60 definition bodies;
3,128,821 bytes; SHA-256
f02858ee2792a2bd407677d2980c6f2b150c6f5d913fc8ffdd9611afe62bc88b.
The prior 3,100,926 bytes remain an exact prefix. All seven new blocks were
read whole. Their axioms are subsets of propext, Classical.choice and Quot.sound.
All 4,518 prior non-Audit Lean, 367 stronger-source and 817 Haskell/Cabal hashes
remain. Audit retains its exact old body after six imports. Fifteen old document
bodies remain exact suffixes.

Actual child dispatch retains its original resource pair and derives the same
returned caller's ProjectionHeap, including outer-success missing actions or
caches. Actual singleton uniqueness compares complete returned fields at
independent successful primitive bounds. The next-entry adapter derives the
full actual Context/Memos, cache invariants, suffix admissions and reservation.
The prefix induction carries these through an actual Trace, starting with only
original admissions for consumed++untouched. No future heap, Context, model or
completion supplier is assumed. The final stopped-call wrapper remains separate.
Arbitrary outer native errors are outside the present heap observer.

Completed child traversals keep the same full result at larger primitive bounds.
Actual cached allocation retains old allocated-slot keys and gives the fresh slot
the original expansion keys. It does not derive a finite key universe or global
termination. Earlier conditional rendered soundness, finite canonical/history/
arity certificates and ordered output-prefix preservation remain unchanged.

The main gap is an actual model-preserving emitted output and an original finite
depth across all preceding allocating callbacks and the chosen continuation.
Captured finalization/callback/whole-driver lineage, complete policy/origin,
public APIs and optimized Haskell correspondence remain open. DONE does not imply
Discharged. Intended partial outputs remain. No new runtime defect is established.

No Haskell source changed. No Haskell build or test ran. No new Haskell defect
or fix was established. FINDINGS retains earlier external repair records.
The three repaired proof lines concern Lean only.

Read ../../notes-current-prepared-child-projection.md for exact contracts and next
work. Board sequence 706 has ID 5c50b197-f0f9-4080-bb8c-bc00027d0422. Exact author,
content and metadata were read back. Publication receipts follow outside this
frozen area. The full goal remains active.
