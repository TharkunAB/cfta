"""Archive the complete immutable recursive ancestry evidence area."""
from pathlib import Path
import hashlib,json,shutil,tarfile
ROOT=Path('/home/tritlo/Code/mcfta');SOURCE=Path('/tmp/mcfta-recursive-ancestry-progress-20261029');DEST=ROOT/'lean/restart-evidence/20261029-recursive-ancestry-progress';DEST.mkdir(exist_ok=False)
seal=json.loads((SOURCE/'FROZEN.json').read_text());assert seal['write_halt'] and seal['full_goal']=='active';expected={v['path']:v for v in seal['payloads']};assert len(expected)==len(seal['payloads']);paths=sorted(p for p in SOURCE.rglob('*') if p.is_file());assert {str(p.relative_to(SOURCE)) for p in paths}==set(expected)|{'FROZEN.json'};records=[]
for path in paths:
 assert not path.is_symlink();data=path.read_bytes();record={'path':str(path.relative_to(SOURCE)),'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}
 if record['path']!='FROZEN.json':assert record==expected[record['path']]
 records.append(record)
archive=DEST/'evidence.tar.gz'
with tarfile.open(archive,'w:gz',compresslevel=6) as target:
 for path in paths:target.add(path,arcname=str(path.relative_to(SOURCE)),recursive=False)
manifest={'archive':archive.name,'archive_bytes':archive.stat().st_size,'archive_sha256':hashlib.sha256(archive.read_bytes()).hexdigest(),'source_commit':seal['source_head'],'docs_commit':seal['docs_head'],'payloads':records};(DEST/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n');shutil.copyfile(ROOT/'lean/restart-evidence/20261029-prepared-ancestry-progress/verify.py',DEST/'verify.py');shutil.copyfile(__file__,DEST/'package.py')
readme=f'''# Recursive output ancestry: complete restart evidence

Source `{seal['source_head']}`. Documentation `{seal['docs_head']}`.
Branch formalize. The complete formalization objective remains ACTIVE.
Read `lean/notes-current-recursive-ancestry-progress.md` for the exact contracts.

Every sealed regular file is archived without a filter. This includes actual
compiler inputs, raw logs, source-only candidates and reviewed scopes, full
public readback, final source and document copies, the original document bodies,
measurements, Git records, exact board requests/readbacks and failed helper
scripts/logs. Historical author UNTESTED labels remain. The final strict-source
mapping identifies the exact versions that Root checked.

Payloads: {len(records):,}. Raw bytes: {sum(v['bytes'] for v in records):,}.
Compressed bytes: {manifest['archive_bytes']:,}.
SHA256: `{manifest['archive_sha256']}`.
The manifest binds every path, byte count and SHA256.

Verify or reconstruct from the repository root:

```sh
python3 lean/restart-evidence/20261029-recursive-ancestry-progress/verify.py lean/restart-evidence/20261029-recursive-ancestry-progress --extract /tmp/mcfta-recursive-ancestry-progress-restored
```

Use a fresh destination. Omit --extract to verify only. The standard-library
verifier rejects duplicate, missing, extra, unsafe and non-regular members.
It executes no Lean or Haskell code. Keep restored evidence immutable. Continue
in a new writable area. The original source area is sealed read-only.

Four additive modules contain six public theorems and four private helpers:
587 lines/35,942 bytes. Valid actual prefixes retain literal slot-history
equality. Actual opaque receipts and ordinary captured completions retain
same-slot key membership. Entry and the actual callback compose that property.
Every ResourceHistory output retains its original keys. The strengthened
original finite producer keeps the same bound/outcome, all-extra work stability,
resources and all admitted histories, and adds retention for every output.
This includes outputs before a stop. No new input gate or future-retention
supplier is added. Enumerator and native definitions are unchanged.

All five exact final strict sources pass. Audit builds 4,599 jobs and checks
81,980 theorem dependencies. All 11 compiler commands pass. All 49 input
snapshots are checked. Compiler jobs remain serial at measured 4 GiB max/high
and zero swap. Two evidence-helper failures and their exact scripts/logs are
preserved separately. No proof candidate failed at this checkpoint.

Public: 833 complete theorem checks/axiom lists,68 definition bodies,
3,473,780 bytes, SHA256
17202f2b56c9064978a289c1e8fb50c995468c2f3f222f815fb96ab75cbdd276.
The prior3,454,104 bytes are an exact prefix; all19,676 added bytes were read.
All4,594 old non-Audit Lean,443 stronger-source and821 integrated Haskell/Cabal
identities remain. All23 old document bodies remain exact suffixes. There are
24 final documents. Prior evidence retains191,012 tracked files in523 areas.
Three proof-scope manifests verify77 identities; diagnostic planning verifies
46 more identities and28 literal review cuts. Copy scope and read scope remain
separate. Only propext, Classical.choice and Quot.sound are allowed.

No Haskell change, new Haskell defect or Haskell check occurred here. FINDINGS
retains parser repair c15021ce706ef560b6c0ab335ceed1a4b67ba4aa for external pickup.
Main remains63aae675c and is an ancestor. The repair is not yet on that main.
The prior successful parser checks were not repeated without a source change.

The semantic claim remains conditional checked rendered soundness under its
contracts, fixed-PCS and whole-Discharged, plus ordered output-prefix retention
at greater depth. DONE does not imply Discharged. Configured stop can emit a
partial result. The new ancestry result proves neither a strict global rank nor
representative transfer, sufficient recursive depth, chosen-model coverage or
physical Haskell correspondence.

Next: actual diagnostic-cache ancestry through closed finite-depth induction.
Per-output history is insufficient when a stopped result has no outputs.
Retain processed pruning receipts, current receipt and nested Failure caches.
The diagnostic-next report gives actual producer insertion points and an
old-bound alignment argument. It is planning only. No diagnostic predicate,
theorem or strengthened depth family is installed.

Native generated-family/original rank, nonterminal chosen-model recursive
emission and original-input sufficient recursive depth remain the main gaps.
Full policy/origin/public API admission and optimized Haskell correspondence
remain open. Existing counterexamples and marked missing historical logs remain.
Board720 has exact author/content/metadata readback. Full goal ACTIVE.
''';(DEST/'README.md').write_text(readme)
summary={'payloads':len(records),'raw_bytes':sum(v['bytes'] for v in records),'archive_bytes':manifest['archive_bytes'],'archive_sha256':manifest['archive_sha256']};print(json.dumps(summary));(Path(__file__).parent/'archive-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
