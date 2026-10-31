from pathlib import Path
import hashlib
import json
import shutil
import tarfile

repo = Path('/home/tritlo/Code/mcfta')
root = Path('/tmp/mcfta-first-child-native-frame-control-20261031')
target = repo / 'lean/restart-evidence/20261031-first-child-native-frame-control'
target.mkdir(exist_ok=False)
seal = json.loads((root / 'FROZEN.json').read_text())
assert seal['write_halt'] and not seal['full_objective_complete']
expected = {row['path']: row for row in seal['payloads']}
root_files = [path for path in sorted(root.rglob('*')) if path.is_file()]
assert {path.relative_to(root).as_posix() for path in root_files} == set(expected) | {'FROZEN.json'}
extra = Path(__file__).parent / 'packaging-after-freeze'
extra_files = [path for path in sorted(extra.rglob('*')) if path.is_file()]
files = [(path.relative_to(root).as_posix(), path) for path in root_files]
files += [('packaging-after-freeze/' + path.relative_to(extra).as_posix(), path) for path in extra_files]
directories = {path.relative_to(root).as_posix() for path in root.rglob('*') if path.is_dir()}
directories.add('packaging-after-freeze')
directories.update('packaging-after-freeze/' + path.relative_to(extra).as_posix()
                   for path in extra.rglob('*') if path.is_dir())
directories = sorted(directories)
rows = []
objects = {}
for relative, path in files:
    assert not path.is_symlink()
    if not relative.startswith('packaging-after-freeze/'):
        assert not path.stat().st_mode & 0o222
    data = path.read_bytes()
    digest = hashlib.sha256(data).hexdigest()
    row = {'path': relative, 'bytes': len(data), 'sha256': digest}
    if relative != 'FROZEN.json' and not relative.startswith('packaging-after-freeze/'):
        assert row == expected[relative]
    rows.append(row)
    objects.setdefault(digest, path)

class SplitWriter:
    def __init__(self):
        self.stream = None
        self.total = 0
        self.size = 0
        self.digest = hashlib.sha256()
        self.part_digest = None
        self.parts = []
        self.name = 'evidence.tar.gz'

    def finish_part(self):
        if self.stream is not None:
            self.stream.close()
            self.parts.append({'path': Path(self.stream.name).name, 'bytes': self.size,
                               'sha256': self.part_digest.hexdigest()})
            self.stream = None

    def write(self, data):
        length = len(data)
        self.digest.update(data)
        while data:
            if self.stream is None:
                self.size = 0
                self.part_digest = hashlib.sha256()
                self.stream = (target / ('evidence.tar.gz.part-' + str(len(self.parts)).zfill(3))).open('xb')
            count = min(len(data), 48_000_000 - self.size)
            piece = data[:count]
            self.stream.write(piece)
            self.part_digest.update(piece)
            self.size += count
            self.total += count
            data = data[count:]
            if self.size == 48_000_000:
                self.finish_part()
        return length

    def flush(self):
        if self.stream is not None:
            self.stream.flush()

    def tell(self):
        return self.total

    def close(self):
        self.finish_part()

writer = SplitWriter()
with tarfile.open(fileobj=writer, mode='w:gz', compresslevel=6) as stream:
    for digest, path in sorted(objects.items()):
        member = tarfile.TarInfo('sha256/' + digest)
        member.size = path.stat().st_size
        member.mode = 0o444
        with path.open('rb') as source:
            stream.addfile(member, source)
writer.close()
assert all(0 < part['bytes'] <= 48_000_000 for part in writer.parts)

manifest = {
    'archive_format': 'sha256-objects-v1', 'archive_storage': 'split-gzip-v1',
    'archive': 'evidence.tar.gz', 'archive_parts': writer.parts,
    'archive_bytes': writer.total,
    'archive_sha256': writer.digest.hexdigest(),
    'source_commit': seal['source_head'], 'docs_commit': seal['docs_head'],
    'directories': directories, 'frozen_control_payloads': len(root_files),
    'packaging_after_freeze_payloads': len(extra_files), 'payloads': rows,
}
(target / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
shutil.copyfile(Path(__file__).with_name('archive-verify.py'), target / 'verify.py')
shutil.copyfile(__file__, target / 'package.py')
readme = f'''# Selected first child and native demand frames: restart evidence

Source `{seal['source_head']}`. Documentation `{seal['docs_head']}`.
Goal ACTIVE. The full original-input objective remains open.
All {len(rows)} regular payload paths and {len(directories)} directories remain.
The archive retains {seal['owners']} complete owners without filtering.
Raw payload bytes: {sum(row['bytes'] for row in rows)}.
Unique objects: {len(objects)}. Compressed bytes: {manifest['archive_bytes']}.
SHA256: `{manifest['archive_sha256']}`.

The archive stores one gzip stream in ordered parts of at most 48 MB.
The manifest verifies every part and the complete concatenated stream.
The original failed 112737869-byte unsplit archive, its failed script and raw,
and the complete packaging repair record remain under packaging-after-freeze.
The frozen control and all source evidence remain exact.

The archive stores each SHA256 object once. The manifest retains every path,
size and hash, including all directories. Extraction creates separate regular
files and no links. The verifier rejects duplicate, missing, extra, unsafe and
non-regular members. All prior provider metadata, seals, failures and board
responses remain. The prior R24 archive stays byte exact in Git.

```sh
python3 lean/restart-evidence/20261031-first-child-native-frame-control/verify.py lean/restart-evidence/20261031-first-child-native-frame-control --extract /tmp/mcfta-first-child-native-frame-restored-20261031
```

Use a fresh destination. Make restored files and directories read-only.
Give each metadata verifier a separate writable output directory.
Use the matching source and documentation checkout. Run verify-current.py,
verify-owned.py, verify-documents.py, verify-peer-replay.py and
verify-prior-evidence.py from the restored area. Also run verify-prior-copy.py and verify-future-targets.py.
These commands repeat no compiler check and run no Haskell product program.

Two current modules have 302 lines and 3 new public laws. Production retains
7 commands, 7 passes, 0 failures and 21 input snapshots. Audit passes 4822 jobs
and 83902 theorem dependencies. Public checks total 1372 with 159 definition
prints and 3 new standard-axiom reports. All previous 5157554 public bytes remain
an exact prefix of 5166348 bytes. All 621 prior protected sources and 835 native
input records stay exact. Audit has only 2 new imports. Every compiler command
has verified 4 GiB max/high before and after, zero swap and a five-minute limit.
Independent source/public/docs review is CLEAR for 302 source lines, 129 public
lines, the 119-line canonical note and 69-line prefix. All seven fresh relocated
review sidecars remain. Scope labels include originalMap/domain, node-count,
table and all other original API obligations.

The earlier isolated first-child/native-frame series retains 11 commands,
2 passes, 9 failures and 156 input snapshots. Its original native source owner
has permanent SCOPE FAIL 101/160. Its original 89-line candidate remains sealed
as UNCOMPILED in that unchanged history. Root retained its separate initial
strict failure and later 94-line strict mathematical repair. The 94-line result
now also passes production checks. No mathematical pass repairs that process
failure. Integrity-only verification does not claim all owners pass scope.

Further captured-cache proof work retains its own whole providers, exact
source versions, diagnostics and status records. It remains separate from
the current two-module production result. The full conjunction-call Post is
retained. Sufficient original depth, common resources, whole recursive ordered
coverage, all public APIs and Haskell correspondence remain open.
No new Haskell defect, edit or fix is established. Record later fixes in FINDINGS.

---

'''
(target / 'README.md').write_text(readme + (repo / 'lean/notes-current-first-child-native-frames.md').read_text())
print(json.dumps({'payloads': len(rows), 'directories': len(directories),
                  'unique_objects': len(objects), 'raw_bytes': sum(row['bytes'] for row in rows),
                  'archive_bytes': manifest['archive_bytes'], 'archive_sha256': manifest['archive_sha256']}))
