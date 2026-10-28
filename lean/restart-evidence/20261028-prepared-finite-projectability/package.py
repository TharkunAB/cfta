"""Archive every regular file in the sealed finite prepared projection proof area."""
from pathlib import Path
import hashlib,json,shutil,tarfile
source=Path('/tmp/mcfta-prepared-finite-projectability-20261028');repo=Path('/home/tritlo/Code/mcfta');dest=repo/'lean/restart-evidence/20261028-prepared-finite-projectability';dest.mkdir(exist_ok=False)
seal=json.loads((source/'FROZEN.json').read_text());assert seal['write_halt'];expected={r['path']:r for r in seal['payloads']};assert len(expected)==len(seal['payloads'])
paths=sorted(p for p in source.rglob('*') if p.is_file());assert {str(p.relative_to(source)) for p in paths}==set(expected)|{'FROZEN.json'};records=[]
for path in paths:
 assert not path.is_symlink();data=path.read_bytes();record=dict(path=str(path.relative_to(source)),bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
 if record['path']!='FROZEN.json':assert record==expected[record['path']]
 records.append(record)
archive=dest/'evidence.tar.gz'
with tarfile.open(archive,'w:gz',compresslevel=6) as tar:
 for path in paths:tar.add(path,arcname=str(path.relative_to(source)),recursive=False)
manifest=dict(archive=archive.name,archive_bytes=archive.stat().st_size,archive_sha256=hashlib.sha256(archive.read_bytes()).hexdigest(),source_commit=seal['source_head'],docs_commit=seal['docs_head'],payloads=records)
(dest/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n');shutil.copyfile(repo/'lean/restart-evidence/20261028-prepared-render-soundness/verify.py',dest/'verify.py');shutil.copyfile(__file__,dest/'package.py')
(dest/'README.md').write_text(f'''# Finite prepared projection: complete evidence

Source: `{seal['source_head']}`. Documentation: `{seal['docs_head']}`.
Branch: formalize. The full formalization goal remains ACTIVE.

Every regular file in the sealed proof area is archived without a filter.
This includes all original failed candidates and full raw logs, separate
repairs, the withdrawn UNTESTED prefix candidate, all compiler input snapshots,
public signatures/axioms and definition bodies, exact source reviews/read scopes,
measurements, prior/final documents, Git receipts and verified board readback.
Historical UNTESTED labels remain unchanged. final-proof-sources.json and
compiler-matrix.json identify final checked source and outcomes.

Payloads: {len(records):,}. Raw bytes: {sum(r['bytes'] for r in records):,}.
Compressed bytes: {manifest['archive_bytes']:,}.
SHA-256: `{manifest['archive_sha256']}`.
Every payload path, byte count and SHA-256 is in manifest.json.

Verify and reconstruct from the repository root:

```sh
python3 lean/restart-evidence/20261028-prepared-finite-projectability/verify.py lean/restart-evidence/20261028-prepared-finite-projectability --extract /tmp/mcfta-prepared-finite-projectability-restored
```

Use a fresh destination. Omit --extract to verify only. The standard-library
verifier checks the archive and every payload. It rejects duplicate, missing,
extra, unsafe and non-regular members. It runs no Lean or Haskell code.
Keep reconstructed data immutable. Continue in a new writable area.

Sixteen modules add sixteen public theorems, two proof-specification predicates,
zero runtime definitions and one private proof helper: 2,166 lines/148,313 bytes.
All sixteen and Audit pass 17 exact strict Lean 4.34.1 checks with warningAsError
and linter.all. Audit passes 4,548 jobs/81,757 theorem dependencies. Thirty-seven
serial commands have 28 passes and nine preserved failures. All final checks
pass. All jobs measure 4 GiB memory.max/high and zero swap. No budget, custom
axiom, native proof evaluation axiom or linter suppression was added.

Public: 731 theorem signatures/axiom lists, 62 definition bodies; 3,273,340 bytes,
SHA-256 bfa4ecefb1665403acc98121146b3db14848a786410df34f38a832e6cfc60125.
The prior 3,156,168 bytes are an exact prefix. All 117,172 new bytes were read,
including recovered display cuts. New axioms use only propext, Classical.choice
and Quot.sound. All 4,531 old non-Audit Lean, 380 stronger-source and 817 Haskell/
Cabal hashes remain unchanged. Audit preserves its old body after 16 imports.
Seventeen old document bodies remain exact suffixes; 18 final documents remain.

The closed finite prepared worker derives supported constraint projection from
original input heap/resources through actual selection, preparation, native
heads, callbacks, receipts, parked/opaque/ordinary branches and ordered siblings.
Complete [] retains its aggregate caller. Stopped some retains that endpoint;
stopped none creates no caller. Each output retains its own native heap.
The final Nat induction discharges the local recursive completion contract.
A combined theorem retains the old bound/outcome/resources/histories/canonical
storage/arity and adds projection at that exact actual outcome.
Stored source handles remain distinct from separately available prepared values.
The existing generic prefix producer suffices. The extra prefix candidate is
withdrawn UNTESTED and preserved. Conditional arity does not imply projection.

Semantic soundness remains conditional on checked rendering, fixed-PCS and
whole-Discharged. Ordered output-prefix retention at larger depth remains.
The principal gap is chosen-model preservation through actual emission and a
sufficient depth derived from source across preceding allocating callbacks.
Stable outcomes at each supplied finite capacity do not derive sufficient depth.
Global key/inventory bounds, full policies/origin/public APIs and optimized
Haskell correspondence remain open. DONE does not imply Discharged. Intended
partial outputs remain in scope. No new all-depth counterexample is established.

The nine failed checks preserve six opaque builds, a redundant strict check of
the first known failed source, and two opaque finite adapter builds. Repairs
concern literal match equations, constructor goal focus, explicit checkEmpty
inference and reduced caller equality. No contract was weakened.
No Haskell source changed, no Haskell check ran and no new Haskell defect/fix
was established. FINDINGS retains all earlier external repair records.

Read ../../notes-current-prepared-finite-projection.md for exact contracts and
next work. Board sequence 708 has ID 885066e2-94a6-4884-a6f2-dac9926e3e8c.
Author/content/metadata have exact verified readback. Final publication receipts
stay outside the frozen area. The full formalization goal remains ACTIVE.
''')
print(json.dumps({k:v for k,v in manifest.items() if k!='payloads'}|dict(payloads=len(records),raw_bytes=sum(r['bytes'] for r in records))))
