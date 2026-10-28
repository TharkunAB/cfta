# Prepared history semantic gates: complete checkpoint evidence

Source commit: `1115481c15dec8193b8d0594366ee5d068c24331`.
Documentation commit: `abc42db95cad2a1e244a394e28e946951d52f4e8`.
Branch: `formalize`. The whole formalization goal remains open and active.

This archive contains every file in the sealed proof area. It includes all
failed drafts and full diagnostics, final strict-check inputs and reports,
complete public readback, exact old-prefix evidence, all 49 whole public block
reviews, the resolved documentation finding, preserved old document bodies,
source hashes, resource measurements, Git receipts and exact board readback.
The root `FROZEN.json` and three final owner seals identify the immutable inputs.
No file filter or cleanup was applied. The original temporary area is immutable.

The archive has 1,832 regular payload files and
45,105,480 uncompressed payload bytes.
`evidence.tar.gz` has 9,183,435 bytes and SHA-256
`5ef2c6192d1a12da427e2f613a82eae861be745fe9d2ce5436060a69f1c6767a`.
`manifest.json` records every payload path, byte count and SHA-256 value.

From the repository root, verify and reconstruct the evidence with one command:

```sh
python3 lean/restart-evidence/20261028-prepared-history-semantics/verify.py lean/restart-evidence/20261028-prepared-history-semantics --extract /tmp/mcfta-prepared-history-semantics-restored
```

Use a fresh destination. Omit `--extract` to verify without reconstruction.
The verifier checks the complete compressed archive and all payload identities.
It rejects duplicate, missing, extra, unsafe and non-regular archive members.
It uses only Python's standard library. It does not invoke Lean or Haskell.
Keep the restored evidence immutable. Use a separate fresh area for later work.

All 30 new modules and Audit pass exact-source strict checks with Lean 4.34.1,
warningAsError and linter.all. The full Audit build passes with 4,463 jobs and
81,374 checked theorem dependencies. Public readback has 622 theorem signatures
with axiom checks and 58 definitions. The old 2,610,680-byte prefix is exact.
The only listed axioms are propext, Classical.choice and Quot.sound.
All 49 new public blocks received whole-block source review.

The checkpoint preserves all 4,432 old non-Audit Lean files, 281 stronger proof
sources, and 817 current Haskell/Cabal files. It preserves all ten older document
bodies exactly. No new Haskell defect or fix was established.
Ten compiler/build failures and one precompiler launch failure remain in the
evidence. All final compiler checks pass. A separate final-review metadata
attempt failed because 28 inherited stronger-source records omit optional byte
counts. The repaired checker retains those original records and checks every
recorded SHA-256, plus byte counts where present. That failed checker is retained.

Current claims and limits are in
`../../notes-current-prepared-history-semantics.md`. The finite producer preserves
canonical trie representation and actual resource histories. Local opaque
semantics, all-tag marker isolation, same-output discharged child retention,
full native Posts and selected preparation arity are checked. Backward arity
still assumes a reached arity certificate. Global stable opaque history evidence,
forward whole-driver arity, whole-history backward semantics, the public
rendering/discharge connection, accepted-output coverage, sufficient recursive
depth, full public APIs and physical Haskell correspondence remain open.

The archived `root-progress-final.json` supersedes earlier progress reports.
Archived Git state was captured before this archive's publication commit.
Use the final branch tip and Git remote readback for publication state.
The earlier reboot archive remains unchanged.
