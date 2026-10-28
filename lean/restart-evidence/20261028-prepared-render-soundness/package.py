"""Archive the complete sealed prepared rendered-soundness evidence."""
from pathlib import Path
import hashlib
import json
import shutil
import tarfile

source = Path('/tmp/mcfta-prepared-producer-arity-20261028')
repo = Path('/home/tritlo/Code/mcfta')
destination = repo / 'lean/restart-evidence/20261028-prepared-render-soundness'
destination.mkdir(parents=True, exist_ok=False)
seal = json.loads((source / 'FROZEN.json').read_text())
assert seal['write_halt'] is True
expected = {record['path']: record for record in seal['payloads']}
assert len(expected) == len(seal['payloads'])
paths = sorted(path for path in source.rglob('*') if path.is_file())
assert {str(path.relative_to(source)) for path in paths} == set(expected) | {'FROZEN.json'}
records = []
for path in paths:
    assert not path.is_symlink()
    raw = path.read_bytes()
    record = dict(path=str(path.relative_to(source)), bytes=len(raw), sha256=hashlib.sha256(raw).hexdigest())
    if record['path'] != 'FROZEN.json':
        assert record == expected[record['path']]
    records.append(record)
archive = destination / 'evidence.tar.gz'
with tarfile.open(archive, 'w:gz', compresslevel=6) as tar:
    for path in paths:
        tar.add(path, arcname=str(path.relative_to(source)), recursive=False)
manifest = dict(archive=archive.name, archive_bytes=archive.stat().st_size,
                archive_sha256=hashlib.sha256(archive.read_bytes()).hexdigest(),
                source_commit=seal['source_head'], docs_commit=seal['docs_head'], payloads=records)
(destination / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
shutil.copyfile(repo / 'lean/restart-evidence/20261028-prepared-point-stability/verify.py', destination / 'verify.py')
shutil.copyfile(Path(__file__), destination / 'package.py')
(destination / 'README.md').write_text(f'''# Prepared finite arity and rendered soundness: complete evidence

Source commit: `{seal['source_head']}`.
Documentation commit: `{seal['docs_head']}`.
Branch: `formalize`. The full formalization goal remains open and active.

The archive contains every regular file in the sealed proof area. No filter or
cleanup was applied. It preserves candidates, installed proof snapshots, strict
inputs, both failed compiler attempts and their full diagnostics, complete
public readbacks, all whole-block contract reviews, source identities, semantic
route reports, prior and final document bodies, resource measurements, Git
receipts, and the exact board request and verified readback.
The source area and all earlier evidence remain immutable.

There are {len(records):,} regular payloads and
{sum(record['bytes'] for record in records):,} uncompressed payload bytes.
The compressed size is {manifest['archive_bytes']:,} bytes.
SHA-256: `{manifest['archive_sha256']}`.
The manifest lists every payload path, byte count and SHA-256 value.

From the repository root, verify and reconstruct it with:

```sh
python3 lean/restart-evidence/20261028-prepared-render-soundness/verify.py lean/restart-evidence/20261028-prepared-render-soundness --extract /tmp/mcfta-prepared-render-soundness-restored
```

Use a fresh destination. Omit `--extract` to verify only. The standard-library
verifier checks the compressed file and every payload. It rejects duplicate,
missing, extra, unsafe and non-regular members. It runs no Lean or Haskell
program. Keep restored data immutable and continue in a new writable area.

All 22 new modules and Audit pass 23 exact final strict Lean 4.34.1 checks.
The flags are warningAsError and linter.all. The combined Audit passes 4,501
jobs and 81,561 theorem dependency checks. Proof budgets did not increase.
There is no linter suppression or added proof axiom. The old unused-variable
warning is confined to its unchanged old source and default Lake replays.

Public readback contains 674 theorem signatures with axiom checks and 60
definitions. All 27 new theorem blocks and two complete definition bodies have
whole-block source review. The prior 2,820,279-byte readback and intermediate
2,975,778-byte arity readback remain exact prefixes. The final 3,016,159-byte
readback has SHA-256
`2178cc6a9cadb3116d8aac56797d0219afe25f380e608126cf049a6204156902`.
Only propext, Classical.choice and Quot.sound occur in the public axiom lists.

All 4,478 prior non-Audit Lean sources, 327 prior stronger proof sources and
817 Haskell/Cabal files retain their hashes. Eleven old document bodies remain
exact suffixes. No Haskell defect or fix was established. No Haskell source
changed and no Haskell check ran. Earlier repair findings remain in FINDINGS.md.
All 39 compiler/build/readback commands retain exact raw diagnostics and measured
4 GiB memory.max/memory.high with zero swap. Two compiler failures are retained;
all final checks pass. The final progress report also records the static-probe
and board-key bookkeeping corrections.

Original prepared finite inputs now derive arity through actual native heads,
callbacks and sibling scans, including aggregate endpoints with empty outputs.
Original histories and canonical storage remain at their exact original bound
and outcome. Actual output models restore original models under whole-cache
Discharged. Actual checked rendering derives original native-root membership
and every original suspended bucket restriction. Initial canonical storage,
genuine original arity, resources and selection remain explicit producer gates.
Whole Discharged, actual rendering Success and checked PCS residuals remain
explicit observer gates. Rendering alone does not establish discharge.

Coverage, sufficient recursive depth, public input/acceptance and PCS-language
connections, counting/ranking/sampling integration and physical optimized
Haskell correspondence remain open. Read
`../../notes-current-prepared-render-soundness.md` for the exact statement and
next proof sequence. The full goal remains active.

`root-progress-final.json` records the final archived progress state. Its Git
receipts precede this archive publication commit.
''')
print(json.dumps({key: value for key, value in manifest.items() if key != 'payloads'} |
                 dict(payloads=len(records), raw_bytes=sum(record['bytes'] for record in records))))
