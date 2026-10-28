"""Archive every payload in the immutable prepared projectability and ancestry proof area."""
from pathlib import Path
import hashlib
import json
import shutil
import tarfile

source = Path('/tmp/mcfta-prepared-projectability-lineage-20261028')
repo = Path('/home/tritlo/Code/mcfta')
destination = repo / 'lean/restart-evidence/20261028-prepared-projectability-lineage'
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
(destination / 'README.md').write_text(f'''# Prepared projectability and ancestry: complete evidence

Source: `{seal['source_head']}`.
Documentation: `{seal['docs_head']}`.
Branch: formalize. The full formalization goal remains active.

Every regular file in the sealed proof area is archived. No filter or cleanup
was applied. This includes exact compiler inputs and raw results, the failed
ancestry candidate and diagnostic, final public readbacks, complete reviews,
source/read-scope manifests, old and current document bodies, measurements,
Git receipts and the exact board request with verified readback. The separate
next-draft-child directory preserves an UNTESTED draft and all its evidence.
It is not one of the checked modules. Earlier archives remain unchanged.

Payloads: {len(records):,}. Uncompressed bytes:
{sum(record['bytes'] for record in records):,}. Compressed bytes:
{manifest['archive_bytes']:,}. SHA-256: `{manifest['archive_sha256']}`.
Every payload path, byte count and SHA-256 is in manifest.json.

Verify and reconstruct from the repository root:

```sh
python3 lean/restart-evidence/20261028-prepared-projectability-lineage/verify.py lean/restart-evidence/20261028-prepared-projectability-lineage --extract /tmp/mcfta-prepared-projectability-lineage-restored
```

Use a fresh destination. Omit --extract to verify only. The standard-library
verifier checks the compressed file and each payload. It rejects duplicate,
missing, extra, unsafe and non-regular members. It runs no Lean or Haskell code.
Keep reconstructed data immutable. Continue in a new writable area.

Six new modules add six public theorems and no definitions. All six and Audit
pass seven exact strict Lean 4.34.1 source checks with warningAsError and
linter.all. Audit passes 4,519 jobs and 81,661 theorem dependency checks.
The fifteen-command matrix has fourteen passes and one preserved failed
ancestry proof attempt. All final checks pass. The repair changes five Lean
simplifier lines, with no contract change. All commands measured 4 GiB
memory.max/high and zero swap. No proof budget increased. No placeholder,
custom axiom, native proof evaluation axiom or linter suppression was added.
An unchanged old source retains its old replay warning.

Public readback: 701 theorem signatures/axiom lists and 60 definition bodies;
3,100,926 bytes; SHA-256
d50f9f8864e9fdf5ded1231ae150a8832135c75ee3322d6d0c74dade00d99247.
The prior 3,080,208 bytes remain an exact prefix. All six new blocks were read
whole. Their axioms are subsets of propext, Classical.choice and Quot.sound.
All 4,512 prior non-Audit Lean, 361 stronger proof and 817 Haskell/Cabal sources
retain their hashes. Fourteen old document bodies remain exact suffixes.

Actual incoming query/write, dispatch, ordered fold and terminal outer-success
returns preserve the exact old resource pair and derive the SAME caller's whole
ProjectionHeap from the ORIGINAL operation caller's ProjectionHeap. Native and
optional-check receipts are aligned through completion uniqueness. The ordered
fold derives next Context/Post/full Memos from the actual singleton producer.
Terminal derives the same next context and incoming availability from original
fold completion and ok_unique. Supported empty/missing returns retain actual
native effects. Arbitrary outer native failures are outside these observers.
Forecast alphabet membership is not projectability. Whole recursive-driver
transport remains open. No future Heap/model/step supplier is an input.

Actual cached assimilation retains each slot's ancestry keys and transfers
source keys to the target on a non-Empty merge. This is not a finite-key or
global termination theorem. Completed Safe supplies live representatives for
the proposed head-wide pending interface. That full ancestry interface remains
unproved. Source and prepared parent remain separate.

Earlier conditional original rendered soundness, finite resources/history/
canonical/arity and exact ordered output-prefix preservation remain unchanged.
Global coverage still needs an actual model-preserving output and an original
finite depth across all earlier allocating callbacks and the continuation.
DONE does not imply Discharged. Intended partial outputs remain. Full selection/
policy/origin lineage, public adapters and physical optimized Haskell
correspondence remain open. No new runtime defect is established.

No Haskell source changed. No Haskell check ran. No new Haskell defect or fix
was established. FINDINGS.md retains every earlier external repair record.
The ancestry proof repair concerns Lean only.

Read ../../notes-current-prepared-projectability-lineage.md for exact contracts
and the next bounded task. The ChildProjectionHeap candidate is UNTESTED;
review and check it before installation. Its source and read scopes are archived.
Board sequence 705 has ID c82b5dde-8043-4084-a2dc-65c820c70f59. Exact author,
content and metadata were read back. Publication receipts follow outside this
frozen area. The full goal remains active.
''')
print(json.dumps({key: value for key, value in manifest.items() if key != 'payloads'} |
                 dict(payloads=len(records), raw_bytes=sum(record['bytes'] for record in records))))
