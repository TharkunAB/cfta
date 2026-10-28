"""Archive every payload in the immutable actual original and prepared head projectability proof area."""
from pathlib import Path
import hashlib
import json
import shutil
import tarfile

source = Path('/tmp/mcfta-prepared-stopped-child-projection-20261028')
repo = Path('/home/tritlo/Code/mcfta')
destination = repo / 'lean/restart-evidence/20261028-prepared-stopped-child-projection'
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
(destination / 'README.md').write_text(f'''# Actual original and prepared head projection: complete evidence

Source: `{seal['source_head']}`.
Documentation: `{seal['docs_head']}`.
Branch: formalize. The full formalization goal remains active.

Every regular file in the sealed proof area is archived without a filter.
This includes all compiler inputs and full raw logs, the three original failed
proof candidates and diagnostics, separate repairs, final public readbacks,
complete reviews, source/read-scope records, prior and final document bodies,
measurements, Git receipts and the board request with verified readback.
Historical UNTESTED labels remain unchanged. final-proof-sources.json and
compiler-matrix.json identify the final checked source and command outcomes.
Earlier archives remain unchanged.

Payloads: {len(records):,}. Uncompressed bytes:
{sum(record['bytes'] for record in records):,}. Compressed bytes:
{manifest['archive_bytes']:,}. SHA-256: `{manifest['archive_sha256']}`.
Every payload path, byte count and SHA-256 is in manifest.json.

Verify and reconstruct from the repository root:

```sh
python3 lean/restart-evidence/20261028-prepared-stopped-child-projection/verify.py lean/restart-evidence/20261028-prepared-stopped-child-projection --extract /tmp/mcfta-prepared-stopped-child-projection-restored
```

Use a fresh destination. Omit --extract to verify only. The standard-library
verifier checks the compressed file and each payload. It rejects duplicate,
missing, extra, unsafe and non-regular members. It runs no Lean or Haskell code.
Keep reconstructed data immutable. Continue in a new writable area.

Seven modules add seven public proof theorems, no runtime definitions and one
private proof helper. Their final source has 556 lines and 34,845 bytes.
All seven and Audit pass eight exact final strict Lean 4.34.1 checks with
warningAsError and linter.all. Audit passes 4,532 jobs and checks axiom dependencies
of 81,692 theorems. Twenty-one serial compiler commands have eighteen passes and
three preserved proof failures. All final checks pass. Repairs concern a
reserved binder, cost unfolding and nested-match/Option.map proof reduction.
They retain the original contracts. All jobs measured 4 GiB memory.max/high and
zero swap. No proof budget, custom axiom, native proof evaluation axiom or linter
suppression was added. An unchanged old module retains its old replay warning.

Public: 715 theorem signatures and axiom lists plus 60 definition bodies;
3,156,168 bytes, SHA-256
f9a0b9f2904ae49acb61ea00abcc0455a88213efa99b657be5550d627c11a2db.
The prior 3,128,821 bytes remain an exact prefix. The full new 27,347-byte suffix
was read. New axioms are subsets of propext, Classical.choice and Quot.sound.
All 4,524 prior non-Audit Lean, 373 stronger-source and 817 Haskell/Cabal hashes
remain unchanged. Audit retains its exact old body after seven new imports.
Sixteen old document bodies remain exact suffixes; seventeen final documents
are preserved with exact identities.

Actual stopped child traversal derives the exact last child's current gates
from original inputs and its completed prefix. It preserves ProjectionHeap at
the actual outer-success stopped caller, including absent actions and caches.
Selected-edge and captured-finalization observers retain every old producer
gate and derive the actual complete or stopped outer-success caller's heap.
Arbitrary outer native errors and excluded result branches are outside the claim.

Both original and distinct prepared CompletedHeadReceipt types derive their
exact reached caller's projection from their original local input projection
and actual supplied receipt. The prepared route uses its own parent availability
and closure. Its stored source handle stays separate from the prepared parent.
No original-receipt cast, false decode equality or future invariant/model gate
is introduced. It does not prove source/prepared language equivalence.

Actual callback recording keeps that same caller and passes it into recursion.
Later recursion can change it. Whole-driver selected-entry preparation, aggregate
recursive returns including empty outputs, and next ordered siblings still need
projection transport. Conditional arity cannot replace the projection heap.
Actual ordinary child allocation plus native writeSlot retains old allocated-
slot key membership and gives the fresh slot original expansion keys. It does
not derive a finite key universe, whole-head ancestry or global termination.

Strongest semantics remains conditional checked rendered soundness under
fixed-PCS and whole-Discharged, with ordered output-prefix retention at increased
recursive depth. The principal gaps are actual model-preserving emission and a
finite depth derived from the original source across preceding allocating
callbacks and the chosen continuation. Global key/inventory budgets, complete
policies/origin/public APIs and optimized Haskell correspondence remain open.
DONE does not imply Discharged. Intended partial outputs remain in scope.

No Haskell source changed. No Haskell build, test or benchmark ran. No new
Haskell defect or fix was established. FINDINGS retains earlier external repair
records. The three repairs affect Lean proofs only.

Read ../../notes-current-prepared-head-projection.md for exact contracts and next
work. Board sequence 707 has ID 986699c3-98df-4c20-9466-e01c10ba0056. Author,
content and metadata have exact verified readback. Publication receipts follow
outside this frozen area. The full goal remains active.
''')
print(json.dumps({key: value for key, value in manifest.items() if key != 'payloads'} |
                 dict(payloads=len(records), raw_bytes=sum(record['bytes'] for record in records))))
