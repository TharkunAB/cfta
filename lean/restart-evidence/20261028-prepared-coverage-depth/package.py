"""Archive the complete sealed prepared coverage and depth evidence."""
from pathlib import Path
import hashlib,json,shutil,tarfile
source=Path('/tmp/mcfta-prepared-coverage-20261028')
repo=Path('/home/tritlo/Code/mcfta')
destination=repo/'lean/restart-evidence/20261028-prepared-coverage-depth'
destination.mkdir(parents=True,exist_ok=False)
seal=json.loads((source/'FROZEN.json').read_text());assert seal['write_halt'] is True
expected={r['path']:r for r in seal['payloads']};assert len(expected)==len(seal['payloads'])
paths=sorted(p for p in source.rglob('*') if p.is_file())
assert {str(p.relative_to(source)) for p in paths}==set(expected)|{'FROZEN.json'}
records=[]
for path in paths:
 assert not path.is_symlink()
 data=path.read_bytes();record=dict(path=str(path.relative_to(source)),bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
 if record['path']!='FROZEN.json':assert record==expected[record['path']]
 records.append(record)
archive=destination/'evidence.tar.gz'
with tarfile.open(archive,'w:gz',compresslevel=6) as tar:
 for path in paths:tar.add(path,arcname=str(path.relative_to(source)),recursive=False)
manifest=dict(archive=archive.name,archive_bytes=archive.stat().st_size,archive_sha256=hashlib.sha256(archive.read_bytes()).hexdigest(),source_commit=seal['source_head'],docs_commit=seal['docs_head'],payloads=records)
(destination/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
shutil.copyfile(repo/'lean/restart-evidence/20261028-prepared-render-soundness/verify.py',destination/'verify.py')
shutil.copyfile(Path(__file__),destination/'package.py')
(destination/'README.md').write_text(f'''# Prepared coverage prerequisites and completed depth: complete evidence

Source commit: `{seal['source_head']}`.
Documentation commit: `{seal['docs_head']}`.
Branch: `formalize`. The full formalization goal remains open and active.

The archive contains every regular file in the sealed proof area. No filter or
cleanup was applied. It preserves all candidates, exact command source inputs,
failed diagnostics, complete public readbacks, whole-block contract reviews,
source identities and read scopes, prior and final document bodies, resource
measurements, Git receipts, and the exact board request and verified readback.
The source area and all earlier evidence remain immutable.

There are {len(records):,} regular payloads and
{sum(r['bytes'] for r in records):,} uncompressed payload bytes.
The compressed size is {manifest['archive_bytes']:,} bytes.
SHA-256: `{manifest['archive_sha256']}`.
The manifest lists every payload path, byte count and SHA-256 value.

From the repository root, verify and reconstruct it with:

```sh
python3 lean/restart-evidence/20261028-prepared-coverage-depth/verify.py lean/restart-evidence/20261028-prepared-coverage-depth --extract /tmp/mcfta-prepared-coverage-depth-restored
```

Use a fresh destination. Omit `--extract` to verify only. The standard-library
verifier checks the compressed file and every payload. It rejects duplicate,
missing, extra, unsafe and non-regular members. It runs no Lean or Haskell
program. Keep reconstructed data immutable. Continue in a new writable area.

Eight new modules add thirteen public theorems and no definitions. All eight
and Audit pass nine exact final strict Lean 4.34.1 checks with warningAsError
and linter.all. The full Audit passes 4,509 jobs and 81,597 theorem dependency
checks. Proof budgets did not increase. No placeholder, custom axiom, native
evaluation axiom or linter suppression was added. The old replay warning stays
in its unchanged old source. The final matrix binds every source identity.

Public readback contains 687 theorem signatures/axiom checks and 60 definitions.
All thirteen new blocks have whole source and emitted-block review. The old
3,016,159-byte and intermediate 3,034,447-byte readbacks remain exact prefixes
of 3,052,362 bytes. The complete final readback SHA-256 is
`89539665e3e9d5bcf45b85e902481ef2f3f39f5b7e5557deb2a1d6b9e6a9d832`.
Only propext, Classical.choice and Quot.sound occur in the new axiom lists.

All 4,500 prior non-Audit Lean files, 349 stronger proof sources and 817
Haskell/Cabal files keep their identities. Twelve old document bodies remain
exact suffixes. All 26 compiler/build/readback commands have complete raw
outputs and measured 4 GiB memory.max/memory.high with zero swap. Twenty-one
pass and five failed attempts remain preserved. All final checks pass.
The progress report records the exact repairs and diagnostic read scope.

Original physical projectability now gives support for every actual prepared
node row. Original live pending work gives some ready selection under the
explicit proper-model/no-stop gates. Actual hook outputs remain in the sibling
scan. An ACTUAL complete prepared run stays exactly equal at greater recursive
depth with fixed work fuel and all other inputs. Actual successful repeated-key
parking preserves counter and strictly reduces the full candidate count.
This bounds consecutive parks. It does not bound later allocating branches.

Conditional original rendered soundness remains unchanged. Global coverage
still needs an actual model-preserving emitted output and one finite depth
for preceding ordered callbacks and the chosen continuation. Completed-depth
stability supplies no completion existence. DONE does not imply Discharged.
Intended partial outputs remain in scope. Complete selector/policy and recursive
projectability lineage, public adapters, counting/ranking/sampling integration
and physical optimized Haskell correspondence remain open.

No Haskell source changed. No Haskell check ran. No new Haskell defect or fix
was established. FINDINGS.md preserves all earlier external repair records.
The new import, name, pattern, width and simplifier repairs concern Lean proofs.

Read `../../notes-current-prepared-coverage-depth.md` for the full current
statement and next bounded proof sequence. The verified board post has sequence
703 and ID `0ace1892-edf9-4d72-a31f-9535b2c53291`.
`root-progress-final.json` records the archived progress state. Publication
receipts follow outside this sealed area. The full goal remains active.
''')
print(json.dumps({k:v for k,v in manifest.items() if k!='payloads'}|dict(payloads=len(records),raw_bytes=sum(r['bytes'] for r in records))))
