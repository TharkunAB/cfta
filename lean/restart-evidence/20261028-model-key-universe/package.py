"""Archive all regular files from the immutable finite model-key proof area."""
from pathlib import Path
import hashlib,json,shutil,tarfile
SOURCE=Path('/tmp/mcfta-model-key-universe-20261028')
ROOT=Path('/home/tritlo/Code/mcfta')
DEST=ROOT/'lean/restart-evidence/20261028-model-key-universe'
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
(DEST/'README.md').write_text(f'''# Original-model history key shapes: complete evidence

Source `{seal['source_head']}`. Documentation `{seal['docs_head']}`.
Branch formalize. The full formalization goal remains ACTIVE and incomplete.
Read lean/notes-current-model-key-universe.md for exact contracts and next work.

Every regular file in the sealed proof area is archived without a filter.
This includes original failed candidates, full raw compiler logs, repairs,
all command input snapshots, public types/axioms and definition bodies,
whole-source and literal-cut read scopes, measurements, prior/final documents,
Git receipts and exact board readback. Historical UNTESTED labels remain.
Final-proof-sources and compiler-matrix identify the checked final versions.

Payloads: {len(records):,}. Raw bytes: {sum(r['bytes']for r in records):,}.
Compressed bytes: {manifest['archive_bytes']:,}.
SHA256: `{manifest['archive_sha256']}`.
Manifest.json records every payload path, byte count and SHA256.

Verify and reconstruct from the repository root:

```sh
python3 lean/restart-evidence/20261028-model-key-universe/verify.py lean/restart-evidence/20261028-model-key-universe --extract /tmp/mcfta-model-key-universe-restored
```

Use a fresh destination. Omit --extract to verify only. The standard-library
verifier checks the archive and every payload. It rejects duplicate, missing,
extra, unsafe and non-regular members. It executes no Lean or Haskell code.
Keep reconstructed evidence immutable. Continue in a new writable directory.

Seventeen additive modules contain 35 public theorems, six private proof
helpers, two finite proof-domain functions and one history predicate:
1,589 lines/84,435 bytes. Enumerator/native/Haskell runtime definitions do
not change. All seventeen plus Audit pass eighteen exact strict Lean 4.34.1
checks with warningAsError=true and linter.all=true. Audit passes 4,572 jobs
and checks 81,854 theorem dependencies. Thirty-nine serial compiler commands
have 37 passes and two preserved draft failures. All final inputs pass.
All measured caps are 4 GiB memory.max/high and zero swap. No budget increase,
custom axiom, native_decide, placeholder or linter suppression was added.

Public: 777 theorem checks/axiom reports and 66 definition bodies;
3,357,308 bytes, SHA256
e070cbd47953ced82b1d1dcab2eba1121d7b43571269ef1c0f413f2ce876e485.
The prior 3,301,695 bytes are an exact prefix. All 55,613 new bytes were read
without a display cut. Only propext, Classical.choice and Quot.sound are
allowed. All 4,554 old non-Audit Lean, 403 stronger-source and 817 Haskell/
Cabal identities remain. Audit preserves its whole old body after seventeen
imports. Nineteen old document bodies remain exact suffixes. Twenty final
documents are retained. Six source-scope manifests verify 194 artifact
identities before document headers. Literal cuts remain literal cuts.

The original model term defines finite complete recursion-key trie shapes.
Original model/origin/canonical evidence derives actual stored-key membership.
KeyAncestry constrains both full history fields at all slots, including stale
fresh-counter ancestry read by allocation. Literal initial histories are empty.
Actual entry derives inserted Mu/explicit-Union key shapes. Actual lower
operations, terminal prefix, raw/incoming dispatch, ordered folds, child caches,
complete/stopped traversal and selected/captured completion retain that carrier.
An actual completed prepared receipt and its actual successful recording call
retain the same original finite carrier. No future model/key supplier is added.
The completed receipt and input model remain explicit original hypotheses.
This does not derive a recursive output, every future callback model, or a
uniform original-source native handle bound and sufficient search depth.

Native-factor audit narrows the handle obligation to actual inserted Mu/Union
boundary identities. FiniteOrdinaryKeys excludes them. Rebase/query completeness
replace the source at each reached heap. Original provenance is not startup
handle identity. Fits/Reserved are local at supplied depth. Need a finite
structural boundary family closed under generated native operations and an
actual handle or cardinality bound along branches. No infinite-handle or
divergence counterexample is admitted. No Haskell defect follows from this gap.

Strongest semantics remains conditional checked rendered soundness under
fixed-PCS/whole-Discharged and ordered output-prefix retention with greater
depth. The biggest gaps are chosen-model recursive emission and original-source
sufficient depth across earlier allocating callbacks. Complete policy/origin/
public API and optimized Haskell correspondence remain open. Configured stop
can emit a partial output. DONE does not imply Discharged.

No Haskell source changed. No Haskell check ran. No new Haskell defect/fix was
established. FINDINGS retains earlier external repair records. The two new
repairs affect only dependent match elaboration and explicit match reduction
in a Lean proof. Their failed inputs and complete logs remain in this archive.

Board sequence 712, post 5b9df506-738e-43ea-93b6-632b37912317, has verified
exact author/content/metadata. Source remote/tracking heads match. Origin/main
is an ancestor. Standing push permission covers the same formalize destination.
The complete goal remains active. Preserve older archives and frozen areas.
''')
print(json.dumps(dict(payloads=len(records),raw_bytes=sum(r['bytes']for r in records),archive_bytes=manifest['archive_bytes'],archive_sha256=manifest['archive_sha256'])))
