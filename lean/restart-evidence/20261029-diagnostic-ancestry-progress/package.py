"""Archive the complete immutable diagnostic ancestry evidence area."""
from pathlib import Path
import hashlib,json,shutil,tarfile
ROOT=Path('/home/tritlo/Code/mcfta');SOURCE=Path('/tmp/mcfta-diagnostic-ancestry-progress-20261029');DEST=ROOT/'lean/restart-evidence/20261029-diagnostic-ancestry-progress';DEST.mkdir(exist_ok=False)
seal=json.loads((SOURCE/'FROZEN.json').read_text());assert seal['write_halt'] and seal['full_goal']=='active';expected={v['path']:v for v in seal['payloads']};assert len(expected)==len(seal['payloads']);paths=sorted(p for p in SOURCE.rglob('*') if p.is_file());assert {str(p.relative_to(SOURCE)) for p in paths}==set(expected)|{'FROZEN.json'};records=[]
for path in paths:
 assert not path.is_symlink();data=path.read_bytes();record={'path':str(path.relative_to(SOURCE)),'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}
 if record['path']!='FROZEN.json':assert record==expected[record['path']]
 records.append(record)
archive=DEST/'evidence.tar.gz'
with tarfile.open(archive,'w:gz',compresslevel=6) as target:
 for path in paths:target.add(path,arcname=str(path.relative_to(SOURCE)),recursive=False)
manifest={'archive':archive.name,'archive_bytes':archive.stat().st_size,'archive_sha256':hashlib.sha256(archive.read_bytes()).hexdigest(),'source_commit':seal['source_head'],'docs_commit':seal['docs_head'],'payloads':records};(DEST/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n');shutil.copyfile(ROOT/'lean/restart-evidence/20261029-recursive-ancestry-progress/verify.py',DEST/'verify.py');shutil.copyfile(__file__,DEST/'package.py')
readme=f'''# Output and diagnostic ancestry: complete restart evidence

Source `{seal['source_head']}`. Documentation `{seal['docs_head']}`.
Branch formalize. The full formalization objective remains ACTIVE.
Read `lean/notes-current-diagnostic-ancestry-progress.md` for the contracts.

Every sealed regular file is archived without a filter. The archive includes
all failed proof drafts and logs, per-command inputs, final checked sources,
public readback, exact review ranges, current and prior document bodies,
source-only reports, measurements and exact board requests/readbacks.
Historical UNTESTED labels remain. The final strict-source mapping identifies
all 15 exact source versions that passed the compiler.

Payloads: {len(records):,}. Raw bytes: {sum(v['bytes'] for v in records):,}.
Compressed bytes: {manifest['archive_bytes']:,}.
SHA256: `{manifest['archive_sha256']}`.
The manifest binds every path, byte count and SHA256.

Verify or reconstruct from the repository root:

```sh
python3 lean/restart-evidence/20261029-diagnostic-ancestry-progress/verify.py lean/restart-evidence/20261029-diagnostic-ancestry-progress --extract /tmp/mcfta-diagnostic-ancestry-progress-restored
```

Use a fresh destination. Omit --extract to verify only. The standard-library
verifier rejects duplicate, missing, extra, unsafe and non-regular members.
It executes no Lean or Haskell code. Keep restored evidence immutable.
Continue in a new writable area. The original source area is sealed read-only.

Fourteen additive modules contain 23 public theorems and five concrete Prop
definitions: 2,225 lines/153,422 bytes. For each finite recursive capacity,
the strengthened original resource theorem preserves the SAME old work bound,
outcome, resources, all-extra stability and every admitted output history.
Every emitted output and every concrete Cached payload in returned stop
failures retains original recursion-key membership at the SAME RAW SLOT.
The diagnostic result includes processed receipts, current receipts and nested
failures, even with no output. It adds no original gate or future supplier.
Raw Core observations and discarded internal caches are outside this claim.
It proves neither a strict global rank nor sufficient recursive depth.

All 15 final strict sources pass warningAsError/all linters. Audit checks
82,040 theorem dependencies in 4,613 jobs. Actual compiler commands: 33 PASS
and four retained failed drafts. All 368 input snapshots match. Compiler jobs
ran serially at measured 4 GiB max/high and zero swap, with five-minute caps.
The old imported unused-variable warning remains visible. No suppression,
custom axiom, placeholder or native_decide was added.

Main public readback: 856 checks/axiom lists, 73 definition bodies,
3,609,022 bytes, SHA256
90f6ea43f27a796e9ecbd3d679a01a41e1e6b17f57f61698352d2e471ef59405.
The old 3,473,780 bytes are an exact prefix. All 135,242 new bytes were read.
The separate generated FailureAncestry body contains 2,392 reviewed bytes.
All 4,598 old non-Audit Lean, 447 stronger and 821 Haskell/Cabal source hashes
remain. All 24 old document bodies remain exact suffixes. There are 25 final
documents. Prior evidence retains 191,017 tracked files in 524 areas.
Complete source copies are distinct from reviewed ranges. Both are retained.

No Haskell change/check/new defect occurred. FINDINGS retains parser repair
c15021ce706ef560b6c0ab335ceed1a4b67ba4aa, its lawful codec reproduction and prior
passing checks. Main63aae675c lacks the repair. External pickup remains needed.

The semantic claim remains conditional checked rendered soundness under its
contracts, fixed PCS and whole-Discharged, plus ordered prefix retention with
greater recursive capacity. DONE does not imply Discharged. Configured stop
can emit partial results. Whole-language completeness remains open.

Next: original-input bounds for actual generated native return degree,
ordered children, optionalBinder construction and memo provenance. The retained
rank proposal is SOURCE-ONLY and UNPROVED. Original closed-root semantic
completion is already derived; it does not bound generated callback syntax.
Per-query bounds on growing heaps do not give a fixed global enumeration rank.
Nonterminal chosen-model emission, sufficient recursive depth, complete
policy/origin/public API contracts and Haskell correspondence remain open.
Preserve all earlier counterexamples and their exact scope.
Board725 has exact author/content/metadata/type/thread readback. Full goal ACTIVE.
'''
(DEST/'README.md').write_text(readme)
print(json.dumps({'payloads':len(records),'raw_bytes':sum(v['bytes'] for v in records),'archive_bytes':manifest['archive_bytes'],'archive_sha256':manifest['archive_sha256']}))
