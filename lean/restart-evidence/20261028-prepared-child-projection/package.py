"""Archive every payload in the immutable actual child-prefix projectability proof area."""
from pathlib import Path
import hashlib
import json
import shutil
import tarfile

source = Path('/tmp/mcfta-prepared-child-projection-20261028')
repo = Path('/home/tritlo/Code/mcfta')
destination = repo / 'lean/restart-evidence/20261028-prepared-child-projection'
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
    data = path.read_bytes()
    record = dict(path=str(path.relative_to(source)), bytes=len(data),
                  sha256=hashlib.sha256(data).hexdigest())
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
shutil.copyfile(repo / 'lean/restart-evidence/20261028-prepared-render-soundness/verify.py',
                destination / 'verify.py')
shutil.copyfile(Path(__file__), destination / 'package.py')
(destination / 'README.md').write_text(f'''# Actual child-prefix preservation: complete evidence

Source: `{seal['source_head']}`.
Documentation: `{seal['docs_head']}`.
Branch: formalize. The full formalization goal remains active.

Every regular file in the sealed proof area is archived without a filter.
This includes exact compiler inputs and complete raw results, both original
failed candidates and diagnostics, final public readbacks, complete reviews,
source/read-scope records, old and current document bodies, measurements,
Git receipts and the board request with verified readback. Historical source-only
or in-progress labels remain unchanged in frozen reports. Final checked source
identities and outcomes are in final-proof-sources.json and compiler-matrix.json.
Earlier archives remain unchanged.

Payloads: {len(records):,}. Uncompressed bytes:
{sum(record['bytes'] for record in records):,}. Compressed bytes:
{manifest['archive_bytes']:,}. SHA-256: `{manifest['archive_sha256']}`.
Every payload path, byte count and SHA-256 is in manifest.json.

Verify and reconstruct from the repository root:

```sh
python3 lean/restart-evidence/20261028-prepared-child-projection/verify.py lean/restart-evidence/20261028-prepared-child-projection --extract /tmp/mcfta-prepared-child-projection-restored
```

Use a fresh destination. Omit --extract to verify only. The standard-library
verifier checks the compressed file and each payload. It rejects duplicate,
missing, extra, unsafe and non-regular members. It runs no Lean or Haskell code.
Keep reconstructed data immutable. Continue in a new writable area.

Six modules add seven public theorems and no definitions or private helpers.
All six and Audit pass seven exact final strict Lean 4.34.1 checks with
warningAsError and linter.all. Audit passes 4,525 jobs and checks axiom
dependencies of 81,676 theorems. The seventeen-command compiler matrix contains
fifteen passes and two preserved failures. All final checks pass. One query
equality line and two simplifier lines were repaired without contract changes.
All commands measured 4 GiB memory.max/high and zero swap. No proof budget,
custom axiom, native proof evaluation axiom or linter suppression was added.
An unchanged old module retains its old replay warning.

Public: 708 theorem signatures/axiom lists and 60 definition bodies;
3,128,821 bytes; SHA-256
f02858ee2792a2bd407677d2980c6f2b150c6f5d913fc8ffdd9611afe62bc88b.
The prior 3,100,926 bytes remain an exact prefix. All seven new blocks were
read whole. Their axioms are subsets of propext, Classical.choice and Quot.sound.
All 4,518 prior non-Audit Lean, 367 stronger-source and 817 Haskell/Cabal hashes
remain. Audit retains its exact old body after six imports. Fifteen old document
bodies remain exact suffixes.

Actual child dispatch retains its original resource pair and derives the same
returned caller's ProjectionHeap, including outer-success missing actions or
caches. Actual singleton uniqueness compares complete returned fields at
independent successful primitive bounds. The next-entry adapter derives the
full actual Context/Memos, cache invariants, suffix admissions and reservation.
The prefix induction carries these through an actual Trace, starting with only
original admissions for consumed++untouched. No future heap, Context, model or
completion supplier is assumed. The final stopped-call wrapper remains separate.
Arbitrary outer native errors are outside the present heap observer.

Completed child traversals keep the same full result at larger primitive bounds.
Actual cached allocation retains old allocated-slot keys and gives the fresh slot
the original expansion keys. It does not derive a finite key universe or global
termination. Earlier conditional rendered soundness, finite canonical/history/
arity certificates and ordered output-prefix preservation remain unchanged.

The main gap is an actual model-preserving emitted output and an original finite
depth across all preceding allocating callbacks and the chosen continuation.
Captured finalization/callback/whole-driver lineage, complete policy/origin,
public APIs and optimized Haskell correspondence remain open. DONE does not imply
Discharged. Intended partial outputs remain. No new runtime defect is established.

No Haskell source changed. No Haskell build or test ran. No new Haskell defect
or fix was established. FINDINGS retains earlier external repair records.
The three repaired proof lines concern Lean only.

Read ../../notes-current-prepared-child-projection.md for exact contracts and next
work. Board sequence 706 has ID 5c50b197-f0f9-4080-bb8c-bc00027d0422. Exact author,
content and metadata were read back. Publication receipts follow outside this
frozen area. The full goal remains active.
''')
print(json.dumps({key: value for key, value in manifest.items() if key != 'payloads'} |
                 dict(payloads=len(records), raw_bytes=sum(record['bytes'] for record in records))))
