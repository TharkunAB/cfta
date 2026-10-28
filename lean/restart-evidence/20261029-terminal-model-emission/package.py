"""Archive all regular files from the immutable terminal emission and boundary budget proof area."""
from pathlib import Path
import hashlib,json,shutil,tarfile
SOURCE=Path('/tmp/mcfta-prepared-model-emission-20261028')
ROOT=Path('/home/tritlo/Code/mcfta')
DEST=ROOT/'lean/restart-evidence/20261029-terminal-model-emission'
DEST.mkdir(exist_ok=False)
seal=json.loads((SOURCE/'FROZEN.json').read_text());assert seal['write_halt']and seal['full_goal']=='active'
expected={r['path']:r for r in seal['payloads']};assert len(expected)==len(seal['payloads'])
paths=sorted(p for p in SOURCE.rglob('*')if p.is_file());assert {str(p.relative_to(SOURCE))for p in paths}==set(expected)|{'FROZEN.json'}
records=[]
for path in paths:
 assert not path.is_symlink();raw=path.read_bytes();record=dict(path=str(path.relative_to(SOURCE)),bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest())
 if record['path']!='FROZEN.json':assert record==expected[record['path']],path
 records.append(record)
archive=DEST/'evidence.tar.gz'
with tarfile.open(archive,'w:gz',compresslevel=6)as target:
 for path in paths:target.add(path,arcname=str(path.relative_to(SOURCE)),recursive=False)
manifest=dict(archive=archive.name,archive_bytes=archive.stat().st_size,archive_sha256=hashlib.sha256(archive.read_bytes()).hexdigest(),source_commit=seal['source_head'],docs_commit=seal['docs_head'],payloads=records)
(DEST/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
shutil.copyfile(ROOT/'lean/restart-evidence/20261028-prepared-model-progress/verify.py',DEST/'verify.py');shutil.copyfile(__file__,DEST/'package.py')
(DEST/'README.md').write_text(f'''# Terminal callback emission and checked boundary budgets: complete evidence

Source `{seal['source_head']}`. Documentation `{seal['docs_head']}`.
Branch formalize. The full formalization goal remains ACTIVE and incomplete.
Read lean/notes-current-terminal-model-emission.md for exact contracts and next work.

Every regular file in the sealed proof area is archived without a filter.
This includes failed candidates, full raw logs and command input snapshots,
repairs, public types/axioms and definition bodies, source read scopes,
measurements, prior/final documents, Git receipts and exact board readback.
Historical UNTESTED labels remain. final-proof-sources.json and the compiler
matrix identify the final checked versions. Literal cuts remain literal cuts.

Payloads: {len(records):,}. Raw bytes: {sum(r['bytes']for r in records):,}.
Compressed bytes: {manifest['archive_bytes']:,}.
SHA256: `{manifest['archive_sha256']}`.
manifest.json records every payload path, byte count and SHA256.

Verify and reconstruct from the repository root:

```sh
python3 lean/restart-evidence/20261029-terminal-model-emission/verify.py lean/restart-evidence/20261029-terminal-model-emission --extract /tmp/mcfta-terminal-model-emission-restored
```

Use a fresh destination. Omit --extract to verify only. The standard-library
verifier checks every archive payload. It rejects duplicate, missing, extra,
unsafe and non-regular members. It executes no Lean or Haskell code.
Keep reconstructed evidence immutable. Continue in a new writable directory.

Eight additive modules contain 10 public theorems, two private proof helpers
and one finite proof-domain function: 518 lines/29,349 bytes. All eight plus
Audit pass nine exact strict Lean 4.34.1 checks. Audit passes 4,580 jobs and
checks 81,876 theorem dependencies. Of 29 serial compiler commands, 24 pass
and five failed drafts are retained. All final inputs pass. Measured caps:
4 GiB memory.max/high and zero swap. No budget increase, custom axiom,
native_decide, placeholder or linter suppression was added.

Public: 787 theorem checks/axiom reports and 67 definition bodies;
3,376,571 bytes, SHA256
b966ceaf09c9ec31ed06c5a6c73bff9fa42205c2292ef0206dac5d92406c5dde.
The prior 3,357,308 bytes are an exact prefix. All 19,263 new bytes were read.
Only propext, Classical.choice and Quot.sound are allowed. All 4,571 old
non-Audit Lean, 420 stronger-source and 817 Haskell/Cabal identities remain.
Audit keeps its whole old body after eight imports. Twenty prior document
bodies are exact suffixes. Twenty-one final documents are retained.
Three source-scope manifests verify 112 artifact identities. The old Audit
identity is checked against retained prior-Audit and its exact current suffix.

The actual prepared terminal callback emits a singleton modeled cache with
the same original assignment. Original selected preparation keeps the same
Mu body degree ceiling. Actual boundary narrowing retains the input value
and heap and selects the identity action. Actual false checking derives
freshness. The original model gives an unused finite per-handle key shape.
Inserting that exact key strictly decreases the local budget. Full indexed
prefix/Entry linkage, a native handle cardinality bound, nonterminal chosen-
output induction and original-source sufficient depth remain open.

The old closed-unfolding witness refutes startup-only Mu inventory and
decreasing cached depth. The original cited native /tmp logs are absent.
The witness does not prove divergence or a Haskell defect. Strongest system
semantics remains conditional checked rendered soundness under fixed-PCS/
whole-Discharged and ordered output-prefix retention at greater depth.
Configured stop can emit partial outputs. DONE does not imply Discharged.

No Haskell source changed. No Haskell check ran. No new Haskell defect or fix
was established. FINDINGS retains earlier external repair records. The five
new failures concern Lean elaboration or strict linting. All failures and
repairs remain. Board sequence 715, post d19b0edb-4621-4612-b18c-387fc1147a16,
has exact verified author/content/metadata. The complete goal stays active.
''')
print(json.dumps(dict(payloads=len(records),raw_bytes=sum(r['bytes']for r in records),archive_bytes=manifest['archive_bytes'],archive_sha256=manifest['archive_sha256'])))
