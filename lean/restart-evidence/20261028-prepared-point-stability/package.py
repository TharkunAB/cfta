"""Archive the complete sealed prepared point evidence."""
from pathlib import Path
import hashlib,json,tarfile,shutil
source=Path('/tmp/mcfta-prepared-point-stability-20261028')
repo=Path('/home/tritlo/Code/mcfta')
destination=repo/'lean/restart-evidence/20261028-prepared-point-stability'
destination.mkdir(parents=True,exist_ok=False)
seal=json.loads((source/'FROZEN.json').read_text());assert seal['write_halt'] is True
expected={r['path']:r for r in seal['payloads']};assert len(expected)==len(seal['payloads'])
paths=sorted(p for p in source.rglob('*') if p.is_file());assert {str(p.relative_to(source)) for p in paths}==set(expected)|{'FROZEN.json'}
records=[]
for p in paths:
 assert not p.is_symlink();b=p.read_bytes();record={'path':str(p.relative_to(source)),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
 if record['path']!='FROZEN.json':assert record==expected[record['path']]
 records.append(record)
archive=destination/'evidence.tar.gz'
with tarfile.open(archive,'w:gz',compresslevel=6) as tar:
 for p in paths:tar.add(p,arcname=str(p.relative_to(source)),recursive=False)
manifest={'archive':archive.name,'archive_bytes':archive.stat().st_size,'archive_sha256':hashlib.sha256(archive.read_bytes()).hexdigest(),'source_commit':seal['source_head'],'docs_commit':seal['docs_head'],'payloads':records}
(destination/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
shutil.copyfile(repo/'lean/restart-evidence/20261028-prepared-history-semantics/verify.py',destination/'verify.py')
shutil.copyfile(Path(__file__),destination/'package.py')
readme=f'''# Prepared point stability and local semantics: complete evidence

Source commit: `{seal['source_head']}`.
Documentation commit: `{seal['docs_head']}`.
Branch: `formalize`. The full goal remains open and active.

The archive contains every regular file in the sealed proof area. No filter or
cleanup was applied. It preserves original candidates, exact installed strict
inputs, all five failed compiler/build attempts and full diagnostics, complete
public readback, all 25 whole-block contract reviews, source identities, arity
route reports, the exact callback obstruction, old and new document bodies,
resource measurements, Git receipts and exact board request/readback.
The source area and all earlier evidence remain immutable.

The archive contains {len(records):,} regular payloads and
{sum(r['bytes'] for r in records):,} uncompressed payload bytes.
Its compressed size is {manifest['archive_bytes']:,} bytes.
SHA-256: `{manifest['archive_sha256']}`.
The manifest lists every payload path, byte count and SHA-256 value.

From the repository root, verify and reconstruct it with:

```sh
python3 lean/restart-evidence/20261028-prepared-point-stability/verify.py lean/restart-evidence/20261028-prepared-point-stability --extract /tmp/mcfta-prepared-point-stability-restored
```

Use a fresh extraction destination. Omit `--extract` to verify only.
The verifier checks the compressed file and every regular payload. It rejects
duplicate, missing, extra, unsafe and non-regular members. It needs only Python's
standard library and runs no Lean or Haskell program. Keep restored inputs
immutable and continue in a separate writable area.

The exact 16 new modules and Audit pass strict Lean 4.34.1 checks with
warningAsError and linter.all. The combined Audit build passes 4,479 jobs and
81,486 theorem dependency checks. Proof budgets did not increase. Public
readback contains 647 theorem signatures with axiom checks and 58 definitions.
The previous 2,760,282-byte readback is an exact prefix. The new 25 theorem
blocks occupy 59,997 bytes and each has whole-block source review. The complete
2,820,279-byte output has SHA-256
`532ea7283b67221f608d8d5f698739553ee2ebe43107f2ee730ffe24b7db3d0a`.
All public axiom lists contain only propext, Classical.choice and Quot.sound.

All 4,462 prior non-Audit Lean sources, 311 prior stronger proof sources and
817 Haskell/Cabal files retain their recorded hashes. Eleven prior document
bodies remain exact suffixes. Earlier complete evidence archives retain their
recorded bytes and SHA-256 values. No new Haskell defect or fix was established.
No Haskell source changed and no Haskell check ran in this checkpoint.
Compiler jobs ran serially under measured 4 GiB memory.max/memory.high and zero
swap limits. The retained old unused-variable replay warning is separate from
the passing strict checks of all new modules and Audit.

The existing HistoryAdmission now pays each actual prepared opaque point.
Successful opaque/terminal points remain identical at larger work bounds.
The local semantic proof retains its explicit bucket-retention and whole reached
Satisfies gates. Local head and opaque completion arity starts at each call's
own input Heap. The whole prepared producer still needs forward arity through
earlier sibling callbacks, including their aggregate caller with empty outputs.
Its original selectionMembers/selectionLength gates remain relevant. Whole
history semantics, public rendering/discharge, accepted-output coverage,
sufficient recursive depth, remaining public APIs and physical Haskell
correspondence remain open.

Read `../../notes-current-prepared-point-stability.md` for the detailed next
proof sequence. `root-progress-final.json` is the final archived progress
report. Archived Git receipts precede this archive publication commit.
'''
(destination/'README.md').write_text(readme)
print(json.dumps({k:v for k,v in manifest.items() if k!='payloads'}|{'payloads':len(records),'raw_bytes':sum(r['bytes'] for r in records)}))
