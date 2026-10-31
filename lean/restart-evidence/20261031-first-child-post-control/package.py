from pathlib import Path
import hashlib
import json
import shutil
import tarfile

repo = Path('/home/tritlo/Code/mcfta')
root = Path('/tmp/mcfta-first-child-post-control-20261031')
target = repo / 'lean/restart-evidence/20261031-first-child-post-control'
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
readme = f'''# Actual successful-child postconditions: restart evidence

Source `{seal['source_head']}`. Documentation `{seal['docs_head']}`.
Goal ACTIVE. The full original-input objective remains open.
All {len(rows)} regular payload paths and {len(directories)} directories remain.
The archive retains {seal['owners']} complete owners without filtering.
Raw payload bytes: {sum(row['bytes'] for row in rows)}.
Unique objects: {len(objects)}. Compressed bytes: {manifest['archive_bytes']}.
SHA256: `{manifest['archive_sha256']}`.

One gzip stream uses ordered parts of at most 48 MB. The manifest verifies
each part and the complete stream. The JSON manifest uses gzip storage when
its plain size exceeds the Git limit. The verifier accepts exactly one
manifest.json or manifest.json.gz. Compression changes no logical field.

Each SHA256 object is stored once. The manifest retains every path, size and
hash, including empty directories. Extraction creates separate regular files.
The verifier rejects duplicate, missing, extra, unsafe and non-regular members.
All provider metadata, seals, failures and board responses remain. The prior
R26 archive stays byte exact in Git. Its complete control and publication
remain retained in this archive.

```sh
python3 lean/restart-evidence/20261031-first-child-post-control/verify.py lean/restart-evidence/20261031-first-child-post-control --extract /tmp/mcfta-first-child-post-restored-20261031
```

Use a fresh destination. Make restored files and directories read-only.
Give each metadata verifier a separate writable output directory. Use the
matching source and documentation checkout. Run verify-current.py,
verify-owned.py, verify-documents.py, verify-peer-replay.py,
verify-prior-evidence.py, verify-prior-copy.py and verify-future-targets.py.
These commands repeat no compiler check and run no Haskell product program.

Current production has five modules, 556 lines and six new laws. All 13 actual
commands pass. All 78 source snapshots remain. Audit has 4832 jobs and 83976
dependencies. Public checks total 1385 with 159 definition prints and six new
standard-axiom reports. All prior 5187699 public bytes remain an exact prefix
of 5210300 bytes. All 628 prior protected sources and 835 native records remain
exact. Audit has only five new imports. Every Lean command has verified 4 GiB
max/high before and after, zero swap and a five-minute limit. Independent
source/public/normalization/docs review is CLEAR for 556 source lines,
333 public lines, the 142-line note and 61-line prefix. The complete peer has
a fresh exact portable relocation and seven restoration sidecars.

The enabled check gives full Post and exact query on all outcomes with the
entry inventory. Successful incoming gives Post with its produced inventory.
Terminal and selected first-child singleton success give full Post and query
at the literal returned Caller. Original staged siblings retain availability,
closure, encoding handles and lookup. Actual split and singleton success are
premises. These laws do not establish success, existence or fuel sufficiency.

Separate next work has five modules, 394 lines and ten laws. Its four complete
Root probes and three complete bounded feedback transactions remain under
future-native-cache-checks. Their strict/public checks passed. All 12 actual
commands, nine passes, three failures and 72 snapshots remain. Failed import
layout, linter and projection checks remain unfiltered. Each whole input
checkpoint, original source version, driver and unknown file remains.

Observed native writes preserve flags and yield canonical count/delta results.
Literal slot writes derive roots and waiting correctness from the original
cache and actual reference replacement. Successful ordinary preparation gives
all five cache fields at the same original heap and actual supplied fuel.
The checked 93-line extension gives these fields for every actual member of
prepareChild Some rows across all Value constructors, including Mu and Union.
The original coherent heap, available closed input, cache components and
reference bound remain premises. No ordinary/nonterminal premise or future
validity supplier is added. These pure helper results do not establish full
recursive execution, Caller/query mutation, or progress.

Root conservatively counts CachedChild lines99–160 as 62/255 OLD lines after
a failed diagnostic exposed the complete interface. Root has 96 total OLD
CFTA lines including inherited views and the same two predeclared wholes.
The author keeps its 125/255 CachedChild hard stop. Full failed diagnostics and
the old interface cut remain opaque to the author and source reviewer.

The old native owner's third-old-file violation remains SCOPE FAIL 101/160.
Its original 89-line candidate remains sealed UNCOMPILED. Root's separate
94-line mathematical pass does not repair this process failure. Integrity-only
replay never claims all owners pass scope. The owned verifier checks all 71
whole owners. It inherits the exact pinned prior result for 70 older literal
source receipts; it does not claim to execute each older receipt again.
The complete prior control copy is checked separately.

Existing chosen-resource child completeness already gives fresh CacheValid,
query identity and reference transport. Existing selected-step completion and
captured Post remain in use. Preserve the distinct CachedOwn and CachedPrepare
caches at their actual worker sites. Actual recursive heap transport, original
depth sufficiency, common resources, remaining schedule and traversal progress
stay open. Keep every original domain/API obligation and Haskell correspondence.
No Haskell defect, edit, fix or product run occurred. Record later fixes in FINDINGS.

---

'''
(target / 'README.md').write_text(readme + (repo / 'lean/notes-current-first-child-post.md').read_text())
print(json.dumps({'manifest': manifest_name, 'payloads': len(rows), 'directories': len(directories),
                  'unique_objects': len(objects), 'raw_bytes': sum(row['bytes'] for row in rows),
                  'archive_bytes': manifest['archive_bytes'], 'archive_sha256': manifest['archive_sha256']}))
