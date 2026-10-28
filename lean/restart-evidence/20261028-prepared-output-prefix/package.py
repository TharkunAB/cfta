"""Archive every payload in the immutable prepared output-prefix proof area."""
from pathlib import Path
import hashlib
import json
import shutil
import tarfile

source = Path('/tmp/mcfta-prepared-output-prefix-20261028')
repo = Path('/home/tritlo/Code/mcfta')
destination = repo / 'lean/restart-evidence/20261028-prepared-output-prefix'
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
(destination / 'README.md').write_text(f'''# Prepared output-prefix proof: complete evidence

Source: `{seal['source_head']}`.
Documentation: `{seal['docs_head']}`.
Branch: `formalize`. The full formalization goal remains active.

Every regular file in the sealed proof area is archived. No filter or cleanup
was applied. The archive preserves candidates, exact compiler source inputs,
all raw diagnostics and readbacks, whole public-contract review, source and
read-scope manifests, old and current document bodies, resource measurements,
Git receipts, the bounded termination audit and the exact verified board note.
Earlier archives and frozen proof areas remain unchanged.

There are {len(records):,} payloads and {sum(record['bytes'] for record in records):,}
uncompressed bytes. The compressed size is {manifest['archive_bytes']:,} bytes.
SHA-256: `{manifest['archive_sha256']}`.
The manifest lists every payload path, byte count and SHA-256 value.

Verify and reconstruct from the repository root:

```sh
python3 lean/restart-evidence/20261028-prepared-output-prefix/verify.py lean/restart-evidence/20261028-prepared-output-prefix --extract /tmp/mcfta-prepared-output-prefix-restored
```

Use a fresh destination. Omit --extract to verify only. The standard-library
verifier checks the compressed file and every payload. It rejects duplicate,
missing, extra, unsafe and non-regular members. It runs no Lean or Haskell code.
Keep reconstructed data immutable. Continue in a new writable area.

Four modules add eight public theorems and no definitions. All four and Audit
pass five exact final strict Lean 4.34.1 checks with warningAsError and linter.all.
All ten compiler commands pass. Audit passes 4,513 jobs and 81,615 theorem
dependency checks. Each command measured 4 GiB memory.max/high and zero swap.
No proof budget increased. No placeholder, custom axiom, native proof evaluation
axiom or linter suppression was added. An old replay warning remains in its
unchanged old source.

Public readback has 695 theorem signatures/axiom lists and 60 definitions.
It has 3,080,208 bytes and SHA-256
5b7ad67458d09c9cb3bee3e57ed513889f15a42e619d8ddc9231b1cf1793a48b.
The prior 3,052,362 bytes remain an exact prefix. All eight new blocks were read
whole. Their axiom lists contain only propext, Classical.choice and Quot.sound.
All 4,508 prior non-Audit Lean, 357 stronger proof and 817 Haskell/Cabal sources
retain their hashes. Thirteen old document bodies remain exact suffixes.

At fixed work fuel and other inputs, the actual prepared search retains every
earlier full output record in order at greater recursive depth. This covers
complete and stopped runs. The original-resource producer derives two stable
actual results under separate original reservations and proves the same prefix
relation at their own sufficient work bounds. Each result retains its own
resource scope. No future output, model or Heap premise was added. The original
Known Heap is explicit. Conditional original rendered soundness is unchanged.

The result does not prove output existence, nonempty output, eventual COMPLETE,
exhaustive model coverage or eventual Discharged rendering. Global coverage
still needs an actual model-preserving emission and one original finite depth
for all earlier ordered allocating callbacks and the chosen continuation.
DONE does not imply Discharged. Intended partial outputs remain in scope.
Public adapters and physical optimized Haskell correspondence remain open.

The bounded termination audit preserves two source-grounded test cases. Neither
has a complete checked Context/Trace replay or establishes a runtime defect.
Closed-Mu local progress exists. Global preservation of an original inventory
or key budget across native merges and allocations remains open.

No Haskell source changed. No Haskell check ran. No new Haskell defect or fix
was established. FINDINGS.md preserves every earlier external repair record.

Read ../../notes-current-prepared-output-prefix.md for exact theorem contracts
and the next bounded proof. Board sequence 704 has ID
c94d8eb0-380e-4c70-8770-19887ee3c5a4. The exact request, response and content/
metadata-verified readback are archived. Publication receipts follow outside
the frozen area. The full goal remains active.
''')
print(json.dumps({key: value for key, value in manifest.items() if key != 'payloads'} |
                 dict(payloads=len(records), raw_bytes=sum(record['bytes'] for record in records))))
