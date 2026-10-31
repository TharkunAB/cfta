from pathlib import Path
import hashlib
import json
import shutil
import tarfile

repo = Path('/home/tritlo/Code/mcfta')
root = Path('/tmp/mcfta-first-child-captured-cache-control-20261031')
target = repo / 'lean/restart-evidence/20261031-first-child-captured-cache-control'
target.mkdir(exist_ok=False)
seal = json.loads((root / 'FROZEN.json').read_text())
assert seal['write_halt'] and not seal['full_objective_complete']
expected = {row['path']: row for row in seal['payloads']}
root_files = [path for path in sorted(root.rglob('*')) if path.is_file()]
assert {path.relative_to(root).as_posix() for path in root_files} == set(expected) | {'FROZEN.json'}
files = [(path.relative_to(root).as_posix(), path) for path in root_files]
directories = sorted(path.relative_to(root).as_posix() for path in root.rglob('*') if path.is_dir())
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
    'packaging_after_freeze_payloads': 0, 'payloads': rows,
}
manifest_data = (json.dumps(manifest, indent=2) + '\n').encode()
manifest_name = 'manifest.json.gz' if len(manifest_data) >= 100_000_000 else 'manifest.json'
if manifest_name.endswith('.gz'):
    import gzip
    with gzip.open(target / manifest_name, 'xb', compresslevel=9) as out:
        out.write(manifest_data)
else:
    (target / manifest_name).write_bytes(manifest_data)
assert (target / manifest_name).stat().st_size < 100_000_000
del manifest_data
shutil.copyfile(Path(__file__).with_name('archive-verify.py'), target / 'verify.py')
shutil.copyfile(__file__, target / 'package.py')
readme = f'''# Actual first-child captured caches: restart evidence

Source `{seal['source_head']}`. Documentation `{seal['docs_head']}`.
Goal ACTIVE. The full original-input objective remains open.
All {len(rows)} regular payload paths and {len(directories)} directories remain.
The archive retains {seal['owners']} complete owners without filtering.
Raw payload bytes: {sum(row['bytes'] for row in rows)}.
Unique objects: {len(objects)}. Compressed bytes: {manifest['archive_bytes']}.
SHA256: `{manifest['archive_sha256']}`.

The archive stores one gzip stream in ordered parts of at most 48 MB.
The manifest verifies every part and the complete concatenated stream.
The JSON manifest uses gzip storage when its plain size exceeds the Git limit.
The verifier accepts exactly one manifest.json or manifest.json.gz.
Manifest compression changes no logical field, path, byte count or hash.

The archive stores each SHA256 object once. The manifest retains every path,
size and hash, including empty directories. Extraction creates separate regular
files and no links. The verifier rejects duplicate, missing, extra, unsafe and
non-regular members. All provider metadata, seals, failures and board responses
remain. The prior R25 archive stays byte exact in Git and its full reconstructed
control and publication remain retained.

```sh
python3 lean/restart-evidence/20261031-first-child-captured-cache-control/verify.py lean/restart-evidence/20261031-first-child-captured-cache-control --extract /tmp/mcfta-first-child-captured-cache-restored-20261031
```

Use a fresh destination. Make restored files and directories read-only.
Give each metadata verifier a separate writable output directory.
Use the matching source and documentation checkout. Run verify-current.py,
verify-owned.py, verify-documents.py, verify-peer-replay.py,
verify-prior-evidence.py, verify-prior-copy.py and verify-future-targets.py.
These commands repeat no compiler check and run no Haskell product program.

Current production has 5 modules, 569 lines and 7 new laws. All 13 commands pass.
All 78 input snapshots remain. Audit has 4827 jobs and 83934 dependencies.
Public checks total 1379 with 159 definition prints and 7 new standard axiom
reports. All previous 5166348 public bytes remain an exact prefix of 5187699.
All 623 prior protected sources and 835 native records remain exact. Audit has
only 5 new imports. Each Lean command has verified 4 GiB max/high before and
after, zero swap and a five-minute limit. Independent source/public/docs review
is CLEAR for 569 source lines, 302 public lines, the 132-line note and 57-line
prefix. The complete review has a fresh exact Root relocation and 7 sidecars.

A separate next increment has 5 modules, 556 lines and 6 laws. Its final strict
and public checks pass. All 27 actual commands, 15 passes, 12 failures and 162
snapshots remain. Its whole provider is isolated-next-first-child-post-checks.
Use FINAL-MANIFEST.json, FINAL-PINS.json and verify-targets-v2.py. The old failed
TARGET seal/helper and the complete directory-order repair remain unchanged.
The author owner original-sibling-entry-review retains its whole providers,
all source versions, old ledgers and exact remaining proof boundary. This
separate increment is outside the current production 5-module result.

The old native owner's third-old-file budget violation remains SCOPE FAIL
101/160. Its original 89-line candidate remains sealed UNCOMPILED. Root's
separate 94-line mathematical pass does not repair this process failure.
Integrity-only replay never claims that all owners pass source scope.

Existing chosen-resource child completeness already supplies fresh CacheValid,
query identity and reference transport. Existing selected-step completion and
captured Post remain reused. Sufficient original depth, common resources,
actual remaining schedule and strict traversal/rank progress stay open.
Keep all original domain and API obligations and Haskell correspondence.
No new Haskell defect, edit or fix is established. Record later fixes in FINDINGS.

---

'''
(target / 'README.md').write_text(readme + (repo / 'lean/notes-current-first-child-captured-cache.md').read_text())
print(json.dumps({'manifest': manifest_name, 'payloads': len(rows), 'directories': len(directories),
                  'unique_objects': len(objects), 'raw_bytes': sum(row['bytes'] for row in rows),
                  'archive_bytes': manifest['archive_bytes'], 'archive_sha256': manifest['archive_sha256']}))
