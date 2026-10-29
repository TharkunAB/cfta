"""Archive every regular file from the immutable prepared ancestry evidence area."""
import hashlib
import json
import shutil
import tarfile
from pathlib import Path

SOURCE = Path('/tmp/mcfta-prepared-ancestry-progress-20261029')
ROOT = Path('/home/tritlo/Code/mcfta')
DEST = ROOT / 'lean/restart-evidence/20261029-prepared-ancestry-progress'
DEST.mkdir(exist_ok=False)
seal = json.loads((SOURCE / 'FROZEN.json').read_text())
assert seal['write_halt'] and seal['full_goal'] == 'active'
expected = {r['path']: r for r in seal['payloads']}
assert len(expected) == len(seal['payloads'])
paths = sorted(p for p in SOURCE.rglob('*') if p.is_file())
assert {str(p.relative_to(SOURCE)) for p in paths} == set(expected) | {'FROZEN.json'}
records = []
for path in paths:
    assert not path.is_symlink()
    raw = path.read_bytes()
    record = dict(path=str(path.relative_to(SOURCE)), bytes=len(raw),
                  sha256=hashlib.sha256(raw).hexdigest())
    if record['path'] != 'FROZEN.json':
        assert record == expected[record['path']], path
    records.append(record)
archive = DEST / 'evidence.tar.gz'
with tarfile.open(archive, 'w:gz', compresslevel=6) as target:
    for path in paths:
        target.add(path, arcname=str(path.relative_to(SOURCE)), recursive=False)
manifest = dict(archive=archive.name, archive_bytes=archive.stat().st_size,
    archive_sha256=hashlib.sha256(archive.read_bytes()).hexdigest(),
    source_commit=seal['source_head'], docs_commit=seal['docs_head'], payloads=records)
(DEST / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
shutil.copyfile(ROOT / 'lean/restart-evidence/20261029-boundary-entry-progress/verify.py', DEST / 'verify.py')
shutil.copyfile(__file__, DEST / 'package.py')
readme = f'''# Prepared ancestry and graph text parser repair: complete evidence

Source `{seal['source_head']}`. Documentation `{seal['docs_head']}`.
Branch formalize. The complete formalization objective remains ACTIVE.
Read lean/notes-current-prepared-ancestry-progress.md for contracts and next work.

Every sealed regular file is archived without a filter. This includes failed
drafts and raw logs, all compiler/native input snapshots, repaired source copies,
public types/axioms and definition bodies, exact source scopes, original/final
documents, measurements, Git records and exact board requests/readbacks.
Historical author UNTESTED labels remain. final-proof-sources.json and
strict-source-mapping.json identify the final compiled versions.

Payloads: {len(records):,}. Raw bytes: {sum(r['bytes'] for r in records):,}.
Compressed bytes: {manifest['archive_bytes']:,}.
SHA256: `{manifest['archive_sha256']}`.
manifest.json binds every payload path, byte count and SHA256.

Verify or reconstruct from the repository root:

```sh
python3 lean/restart-evidence/20261029-prepared-ancestry-progress/verify.py lean/restart-evidence/20261029-prepared-ancestry-progress --extract /tmp/mcfta-prepared-ancestry-progress-restored
```

Use a fresh destination. Omit --extract to verify only. The standard-library
verifier rejects duplicate, missing, extra, unsafe and non-regular members.
It executes no Lean or Haskell code. Keep reconstructed evidence immutable.
Continue in a new writable directory.

Eleven additive proof modules contain 33 public theorems, one retention predicate
and six private proof helpers: 1,295 lines/70,783 bytes. They prove actual all-slot
recursion-key membership retention through storage, terminal assimilation,
child dispatch/traversal and captured prepared heads. They compare the SAME RAW
slot and a FIXED handle for unused-shape budget nonincrease. This is no strict
global rank or representative-transfer theorem. Finalization clears expansion
ancestry; rejected/stopped attached caches retain their input expansion history.
No future-retention/model/carrier supplier is added to the local observers.
Enumerator and native definitions are unchanged.

All 12 exact final strict sources including Audit pass. Audit: 4,595 jobs checks
81,958 theorem dependencies. Compiler: 28 commands, 25 PASS and 3 preserved draft FAIL.
Five native commands: four PASS and one initial Nix linker environment FAIL. One
wrapper argument error ran no compiler. All measured caps remain 4 GiB max/high,
swap 0, with serial compiler/native jobs. All 318 input snapshots are checked.
Only propext, Classical.choice and Quot.sound are allowed. No custom axiom,
native_decide, placeholder, cap increase or linter suppression was added.

Public: 827 theorem checks/axiom lists and 68 complete definition bodies,
3,454,104 bytes SHA256
0192c4d3d92d5ec0096c40a14a0af058abebd6b5918265a8e0a78c7f1b6a8f70.
Prior 3,408,116 bytes are an exact prefix. All 45,988 new bytes were read in four
contiguous ranges. All 4,583 old non-Audit Lean and 432 stronger-source identities
remain. Audit retains its entire old body after 11 imports. All 22 prior document
bodies remain exact suffixes; 23 final documents are retained. Nine source-scope
manifests verify 266 identity records at 226 retained paths. Literal cuts remain
cuts. The worker-next report is source-only planning with 49 whole identities;
copied source bodies and reviewed cuts are distinguished. It adds no theorem.

PR188 graph text serialization is integrated from main
63aae675c5c6b8312bc5872fff065a7de3629aef at merge
e216346905cfeb0b243799138b4c254a739de0aa. Root reproduced four toPathTrie exceptions
for strict-prefix equality paths, using the lawful StateCodec id Right text
codec. Both equal(...) and explicit class syntax reached the partial constructor.
The checked helper now rejects such classes before trie construction. Four
existing malformed-list cases and the format README cover the restriction.
Repair c15021ce706ef560b6c0ab335ceed1a4b67ba4aa is pushed on formalize. It is not
in main at the recorded head. FINDINGS has the exact external pickup record.

After repair: four bad inputs return Left; four valid controls still return Right.
The suite passes 19 examples/0 failures with -Werror. Fourmolu, Cabal-gild,
HLint 3.10 and package metadata checks pass. Two of 821 integrated Haskell/Cabal
identities change; 819 retain their hashes. All 817 inherited manifest identities
remain. The initial Nix libgmp linker failure is separate and preserved. The
host PATH workaround is recorded. The pre-fix probe catches exceptions and
exits zero: assess its eight labeled results, not the exit code alone.

Strongest system semantics remains conditional checked rendered soundness under
fixed-PCS/whole-Discharged and ordered output-prefix retention at greater depth.
DONE does not imply Discharged. Configured stop can emit partial outputs.
Main gaps remain native generated boundary closure/rank, nonterminal original-
model emission, original-input sufficient recursive depth across earlier
allocating/stopped callbacks, full policies/origin/public API and physical
optimized Haskell correspondence. Existing counterexamples remain unchanged.

Next local proofs: all-tag prefix ancestry, actual opaque-cache ancestry and
Entry/SelectedHistoryReceipt composition. ResourceHistory can then give output
retention without another finite-depth proof family. Actual attached stopped
caches require a diagnostic-cache relation and stronger closed finite induction.
Do not assume future hook outputs preserve history. Preserve each callback's
own admitted cache and the reset captured input for siblings. The planning
report's interfaces are uncompiled proposals, not installed results.

Board 717 records the parser repair; board 718 records the checked proof progress.
Both have exact author/content/metadata readback. The complete goal is ACTIVE.
'''
(DEST / 'README.md').write_text(readme)
print(json.dumps(dict(payloads=len(records), raw_bytes=sum(r['bytes'] for r in records),
    archive_bytes=manifest['archive_bytes'], archive_sha256=manifest['archive_sha256'])))
