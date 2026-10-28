"""Archive all regular files from the immutable actual boundary entry progress proof area."""
from pathlib import Path
import hashlib,json,shutil,tarfile
SOURCE=Path('/tmp/mcfta-boundary-entry-progress-20261029')
ROOT=Path('/home/tritlo/Code/mcfta')
DEST=ROOT/'lean/restart-evidence/20261029-boundary-entry-progress'
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
shutil.copyfile(ROOT/'lean/restart-evidence/20261029-terminal-model-emission/verify.py',DEST/'verify.py');shutil.copyfile(__file__,DEST/'package.py')
(DEST/'README.md').write_text(f'''# Actual boundary entry progress: complete evidence

Source `{seal['source_head']}`. Documentation `{seal['docs_head']}`.
Branch formalize. The full formalization objective remains ACTIVE and incomplete.
Read lean/notes-current-boundary-entry-progress.md for exact contracts and next work.

Every regular file in the sealed proof area is archived without a filter.
This includes failed drafts, full raw logs and all command input snapshots,
repairs, public types/axioms and definition bodies, precise source read scopes,
measurements, prior/final documents, Git receipts and exact board readback.
Historical UNTESTED labels remain. final-proof-sources.json and compiler-matrix.json
identify the final checked versions. Literal cuts remain literal cuts.

Payloads: {len(records):,}. Raw bytes: {sum(r['bytes']for r in records):,}.
Compressed bytes: {manifest['archive_bytes']:,}.
SHA256: `{manifest['archive_sha256']}`.
manifest.json records every payload path, byte count and SHA256.

Verify and reconstruct from the repository root:

```sh
python3 lean/restart-evidence/20261029-boundary-entry-progress/verify.py lean/restart-evidence/20261029-boundary-entry-progress --extract /tmp/mcfta-boundary-entry-progress-restored
```

Use a fresh destination. Omit --extract to verify only. The standard-library
verifier checks every payload. It rejects duplicate, missing, extra, unsafe
and non-regular members. It executes no Lean or Haskell code. Keep restored
evidence immutable. Continue in a new writable directory.

Four additive modules contain seven public theorems: 580 lines/37,367 bytes.
No new runtime/specification definitions or private proof helpers are added.
All four plus Audit pass five exact strict Lean 4.34.1 checks. Audit passes
4,584 jobs and checks 81,886 theorem dependencies. Of 19 serial compiler
commands, 14 pass and five failed drafts are retained. All final inputs pass.
Every measured cap is 4 GiB memory.max/high and zero swap. No budget increase,
custom axiom, native_decide, placeholder or linter suppression was added.

Public: 794 theorem checks/axiom lists and 67 definition bodies;
3,408,116 bytes, SHA256
5fbeccbfcc8cbc35107512f25694593b0e38585c34b3ee4968f6afe30cf06216.
Prior 3,376,571 bytes are an exact prefix. All 31,545 new bytes were read.
Only propext, Classical.choice and Quot.sound are allowed. All 4,579 old
non-Audit Lean, 428 stronger-source and 817 Haskell/Cabal identities remain.
Audit keeps its whole old body after four imports. Twenty-one prior document
bodies are exact suffixes; 22 final documents are retained. Three source-scope
manifests verify 95 artifact identities. Eighty-five command snapshots are checked.

The actual narrowed boundary prefix derives exact caller/cache/index/metadata
retention, the same checked handle/bucket, original returned Packet/Ready and
key freshness. That Packet constructs actual completed Entry and native
preparation. Entry consumes the finite original-model shape budget in its
returned expansion history. Every per-slot history stays original. Direct
cached child allocation inherits the strict decrease at the SAME CHECKED
native handle. The child's own native handle can differ. The original-packet
producer derives its own sufficient prefix bound and supplies no future
validity, freshness, model, key membership or Entry success hypothesis.
The actual supported reached boundary observation remains explicit. Prefix
and preparation bounds remain local. No global recursive bound is claimed.

A source-only native audit adds no theorem and ran no evaluator. It identifies
the generated callback body's strict original degree bound as the missing
link before optionalBinder. The old OpenBodyBoundary refutes universal first-
order preparation at a native site. Its exact native_returned theorem observes
only returned=some(.mu 26), not payload/cache equality. It proves neither
divergence nor failure of the original degree ceiling. Physical probe-key and
guard closure, and later queries over generated operands, remain separate.
The older NoNewMu/cached-depth counterexample remains unchanged.

Strongest system semantics remains conditional checked rendered soundness
under fixed-PCS/whole-Discharged and ordered output-prefix retention at greater
depth. Previous actual terminal callback emission remains. Main gaps are
native descriptor closure/rank, nonterminal chosen-model emission and source-
derived sufficient recursive depth across earlier allocating/stopped callbacks.
Full policy/origin/public API and optimized Haskell correspondence remain.
Configured stop can emit partial outputs. DONE does not imply Discharged.

No Haskell source changed. No Haskell check ran. No new Haskell defect or fix
was established. FINDINGS retains all earlier repair records. The five failures
concern new Lean elaboration/reduction and strict instance scoping. Full failed
inputs and repairs remain. Board 716, post a7139029-491a-484d-a1ae-32b612ba728e,
has exact verified author/content/metadata. The complete goal stays ACTIVE.
''')
print(json.dumps(dict(payloads=len(records),raw_bytes=sum(r['bytes']for r in records),archive_bytes=manifest['archive_bytes'],archive_sha256=manifest['archive_sha256'])))
