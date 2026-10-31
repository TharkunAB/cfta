from pathlib import Path
import hashlib
import json
import shutil
import tarfile

repo = Path('/home/tritlo/Code/mcfta')
root = Path('/tmp/mcfta-current-call-probes-control-20261031')
target = repo / 'lean/restart-evidence/20261031-current-call-probes-control'
target.mkdir(exist_ok=False)
seal = json.loads((root / 'FROZEN.json').read_text())
assert seal['write_halt'] and not seal['full_objective_complete']
expected = {row['path']: row for row in seal['payloads']}
files = [path for path in sorted(root.rglob('*')) if path.is_file()]
assert {path.relative_to(root).as_posix() for path in files} == set(expected) | {'FROZEN.json'}
directories = sorted(path.relative_to(root).as_posix() for path in root.rglob('*') if path.is_dir())
rows = []
objects = {}
for path in files:
    assert not path.is_symlink() and not path.stat().st_mode & 0o222
    data = path.read_bytes()
    digest = hashlib.sha256(data).hexdigest()
    row = {'path': path.relative_to(root).as_posix(), 'bytes': len(data), 'sha256': digest}
    if row['path'] != 'FROZEN.json':
        assert row == expected[row['path']]
    rows.append(row)
    objects.setdefault(digest, path)
archive = target / 'evidence.tar.gz'
with tarfile.open(archive, 'w:gz', compresslevel=6) as stream:
    for digest, path in sorted(objects.items()):
        member = tarfile.TarInfo('sha256/' + digest)
        member.size = path.stat().st_size
        member.mode = 0o444
        with path.open('rb') as source:
            stream.addfile(member, source)
assert archive.stat().st_size < 100_000_000
manifest = {
    'archive_format': 'sha256-objects-v1', 'archive': archive.name,
    'archive_bytes': archive.stat().st_size,
    'archive_sha256': hashlib.sha256(archive.read_bytes()).hexdigest(),
    'source_commit': seal['source_head'], 'docs_commit': seal['docs_head'],
    'directories': directories, 'frozen_control_payloads': len(files),
    'packaging_after_freeze_payloads': 0, 'payloads': rows,
}
(target / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
shutil.copyfile(Path(__file__).with_name('archive-verify.py'), target / 'verify.py')
shutil.copyfile(__file__, target / 'package.py')
readme = f'''# Full actual conjunction-call Post: restart evidence

Source `{seal['source_head']}`. Documentation `{seal['docs_head']}`.
Goal ACTIVE. The full original-input objective remains open.
All {len(rows)} regular payload paths and {len(directories)} directories remain.
The archive retains {seal['owners']} complete owners without filtering.
Raw payload bytes: {sum(row['bytes'] for row in rows)}.
Unique objects: {len(objects)}. Compressed bytes: {manifest['archive_bytes']}.
SHA256: `{manifest['archive_sha256']}`.

Each SHA256 object occurs once in the archive. The manifest keeps every original
path, size and hash. Extraction creates a separate regular file at every path.
The verifier rejects duplicate, missing, extra, unsafe and non-regular members.
It restores every directory, including empty directories. It creates no links.
All prior provider metadata, seals, failures and board responses remain.
The prior R23 archive stays exact in Git.

```sh
python3 lean/restart-evidence/20261031-current-call-probes-control/verify.py lean/restart-evidence/20261031-current-call-probes-control --extract /tmp/mcfta-current-call-probes-restored-20261031
```

Use a fresh destination. Make restored files and directories read-only.
Give each metadata verifier a separate writable output directory.
Use the matching source and documentation checkout. Run verify-current.py,
verify-owned.py, verify-documents.py, verify-peer-replay.py and
verify-prior-evidence.py from the restored area. These commands repeat no
compiler check and run no Haskell product program.

Seven current modules have 794 lines and 18 public theorems. The full actual
allocated-conjunction Post follows from the original Context and resident closed
query at the literal returned Caller. All eight Context fields and all three
Post effects/extensions hold. The original inventory and external memos stay
the same. Every outcome keeps its actual stopping state. Mu, Union and signed
paths remain in scope. No future Post, Ready, trace, callback, probe, ordinary-only
or NoNewMu certificate is added. General legal equality instances remain general.
True emptiness excludes satisfying terms. False has no witness guarantee.

The current production series retains 19 commands, 17 passes, two initial proof
failures and 139 input snapshots. All seven final default and strict checks pass.
Audit passes 4820 jobs and 83881 dependencies. Public checks total 1369, with
159 definition prints and 18 new standard axiom reports. The prior 5138887 public
bytes stay an exact prefix of 5157554 bytes. All 614 prior protected records and
835 native input records stay exact. Audit has only seven new imports.
All Lean checks use serial verified 4 GiB max/high, zero swap and five minutes.
No invariant or linter requirement was disabled.

The independent review is CLEAR for seven current modules (794 lines), 267 public lines, the 136-line
canonical note and 74-line prefix. Its historical 63-owner input is complete. All 46804 review-owner files
and 5201 directories remain. All seven fresh-restoration sidecars remain.

One later native-prefix owner has permanent SCOPE FAIL status. It read 101/160
lines of a third OLD original. Its original 89-line candidate was sealed as UNCOMPILED. Root later checked that
original and retained its failed strict result.
The failed scope assertion still fails. Integrity verification does not change
that result. Root's later isolated 94-line mathematical proof passes strict
checking. That separate result does not repair the failed source-read process.
The complete failed owner, offending acquisition, vectors and diagnostics remain.
Separate future first-child/native-frame work and its checks are classified by
their retained status records. They do not change the current seven-module production claim.

Existing finite-D laws give stable actual outcomes and resource paths under
their gates. Those outcomes can still exhaust. Deriving sufficient original
depth and progress to the requested prefix remains open for both workers.
The recursive proof must restore the same captured sibling cache at the actual
after-hook Caller/query and derive the original admission, identity, Fits,
annotation, reservation and common-resource premises there. Local selected-step
and captured-cache Post producers already exist. Prepared None supplies no
hidden outer Caller. Full native operand/frame induction, public order/coverage,
all required APIs and host/Haskell correspondence remain open.
No new Haskell defect, edit or fix is established. Record later fixes in FINDINGS.

---

'''
(target / 'README.md').write_text(readme + (repo / 'lean/notes-current-conjunction-call-post.md').read_text())
print(json.dumps({'payloads': len(rows), 'directories': len(directories),
                  'unique_objects': len(objects), 'raw_bytes': sum(row['bytes'] for row in rows),
                  'archive_bytes': manifest['archive_bytes'], 'archive_sha256': manifest['archive_sha256']}))
