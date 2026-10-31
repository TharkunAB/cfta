from pathlib import Path
import hashlib, json, shutil, tarfile

repo = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-warm-forest-probes-control-20261031')
dest = repo / 'lean/restart-evidence/20261031-warm-forest-probes-control'
dest.mkdir(exist_ok=False)
seal = json.loads((area / 'FROZEN.json').read_text())
assert seal['write_halt'] and seal['goal_turn'] == 'progress' and not seal['full_objective_complete']
expected = {row['path']: row for row in seal['payloads']}
paths = sorted(area.rglob('*'))
assert all(not path.is_symlink() for path in paths)
files = [path for path in paths if path.is_file()]
assert {str(path.relative_to(area)) for path in files} == set(expected) | {'FROZEN.json'}
rows = []
objects = {}
directories = {str(path.relative_to(area)) for path in paths if path.is_dir()}
for path in files:
    assert not path.stat().st_mode & 0o222
    data = path.read_bytes()
    digest = hashlib.sha256(data).hexdigest()
    row = {'path': str(path.relative_to(area)), 'bytes': len(data), 'sha256': digest}
    if row['path'] != 'FROZEN.json':
        assert row == expected[row['path']]
    rows.append(row)
    objects.setdefault(digest, path)
repair = Path(__file__).with_name('format-repair-record')
assert repair.is_dir()
directories.add('packaging-after-freeze')
for path in sorted(repair.rglob('*')):
    assert not path.is_symlink()
    name = 'packaging-after-freeze/' + str(path.relative_to(repair))
    if path.is_dir():
        directories.add(name)
    else:
        data = path.read_bytes()
        digest = hashlib.sha256(data).hexdigest()
        rows.append({'path': name, 'bytes': len(data), 'sha256': digest})
        objects.setdefault(digest, path)
archive = dest / 'evidence.tar.gz'
with tarfile.open(archive, 'w:gz', compresslevel=6) as target:
    for digest, path in sorted(objects.items()):
        info = tarfile.TarInfo('sha256/' + digest)
        info.size = path.stat().st_size
        info.mode = 0o444
        with path.open('rb') as source:
            target.addfile(info, source)
manifest = {'archive_format': 'sha256-objects-v1', 'archive': archive.name,
            'archive_bytes': archive.stat().st_size,
            'archive_sha256': hashlib.sha256(archive.read_bytes()).hexdigest(),
            'source_commit': seal['source_head'], 'docs_commit': seal['docs_head'],
            'directories': sorted(directories), 'frozen_control_payloads': len(files),
            'packaging_after_freeze_payloads': len(rows) - len(files), 'payloads': rows}
(dest / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
shutil.copyfile(Path(__file__).with_name('archive-verify.py'), dest / 'verify.py')
shutil.copyfile(__file__, dest / 'package.py')
readme = f'''# Actual call readiness and probe births: restart evidence

Source `{seal['source_head']}`. Documentation `{seal['docs_head']}`.
Goal ACTIVE. The full original-input objective remains open.
All {len(rows)} regular payload paths remain. All {seal['owners']} complete owners remain.
Raw payload bytes: {sum(row['bytes'] for row in rows)}.
Unique payload objects: {len(objects)}. Compressed bytes: {manifest['archive_bytes']}.
SHA256: `{manifest['archive_sha256']}`.

The archive stores each SHA256 object once. The manifest retains every original
path, size and hash. Extraction creates a separate regular file at every path.
The verifier rejects duplicate, missing, extra, unsafe and non-regular members.
It checks every restored file against its original size and hash.
It restores and checks the complete directory vector, including empty directories.
It does not use symbolic links or hard links. No owner closure is filtered.
The prior R22 archive remains exact in Git. The new format was checked by a
fresh restoration and direct byte comparison of all 21248 prior payloads.
The first new extraction retained every file but omitted empty directories.
The peer directory check rejected that extraction. The complete failed package
and metadata diagnostics remain under packaging-after-freeze. Those later
packaging records are separate from the unchanged frozen control payloads.

```sh
python3 lean/restart-evidence/20261031-warm-forest-probes-control/verify.py lean/restart-evidence/20261031-warm-forest-probes-control --extract /tmp/mcfta-warm-forest-probes-restored-20261031
```

Use a fresh destination. Omit --extract to verify only.
Make restored files read-only. Give each metadata verifier a separate writable
output directory. Use the matching source and documentation checkout.
Run verify-current.py, verify-owned.py, verify-documents.py,
verify-peer-replay.py and verify-prior-evidence.py from the restored area.
These checks run no Lean or Haskell program.

Four production modules have 587 lines and 14 public theorems. Actual forest,
rows and worklist calls derive full physical Effects/Ready on every outcome.
Allocated calls retain the actual heap and equality cache. Actual stored
unfolding retains ProbeHeap, including new nested Mu records.
All 11 production commands pass and retain 45 snapshots.
Audit passes 4813 jobs and 83820 dependencies. Public output has 1351 checks,
159 definitions and 14 new standard axiom reports. The prior 5125851 bytes
remain an exact prefix of 5138887 bytes. All 610 prior protected sources and
835 native inputs remain exact. Audit has only four added imports.

The historical56-owner review input remains immutable. Later isolated proofs
remain separate from production4/587: ExposureProbes133, caller table Sound42,
project/forest ProbeHeap209 and actual ClassScan.Ready49. The last proof derives
native.good through the existing advance_ready producer. Physical Ready alone
does not imply ClassScan.Ready. All original drafts, repairs, receipts, source
vectors and complete provider trees remain. The future shared provider records
four Lean commands, three passes, one import failure and 26 snapshots. It also
retains four partial snapshots from a zero-Lean Python harness failure. Its
outer-log-incident.json states the overwritten historical outer-log limit.
All actual Lean commands use serial verified 4 GiB memory.max/high, zero swap
and a five-minute timeout. No linter or invariant requirement was disabled.

Full actual caller Context/Post and outer rows/worklist probe composition
remain outside this production checkpoint. True excludes all satisfying terms.
False supplies no nonempty witness. The largest global gap remains actual
fixed-original-D execution induction for both workers, with the same captured
sibling cache at the actual post-hook Caller/query and original resource bounds.
Prepared endpoint None supplies no hidden outer Caller certificate.
Public ordered coverage, generic APIs and host/Haskell correspondence remain
open. Mu, Union and opaque values remain in scope.
No Haskell defect, edit or fix was established. No native product program ran.
Record any later Haskell fix in FINDINGS.

---

'''
(dest / 'README.md').write_text(readme + (repo / 'lean/notes-current-call-readiness-and-probe-births.md').read_text())
print(json.dumps({'payloads': len(rows), 'unique_objects': len(objects),
                  'raw_bytes': sum(row['bytes'] for row in rows),
                  'archive_bytes': manifest['archive_bytes'], 'archive_sha256': manifest['archive_sha256']}))
