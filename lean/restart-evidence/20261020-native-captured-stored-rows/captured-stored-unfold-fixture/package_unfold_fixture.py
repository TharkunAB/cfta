from pathlib import Path
import hashlib,json,shutil
h=Path(__file__).resolve().parent
root=Path('/home/tritlo/Code/mcfta')
old=Path('/tmp/mcfta-native-nested-mu-row-capture-fixture')
def sha(data):return hashlib.sha256(data).hexdigest()
def write(name,obj):(h/name).write_text(json.dumps(obj,indent=2)+'\n')
attempts={'unfold-kernels-direct-1':1,'unfold-kernels-direct-2':0,'unfold-kernels-public-1':0}
write('unfold-kernels-selection.json',dict(finalized=True,public_heads=['MicroCFTA.CapturedStoredUnfoldFixture.actual_captured_unfold'],strict='unfold-kernels-direct-2',groups=[dict(name='unfold-kernels-public-1',pairs=1,kind='constructed',full_proof=True)],attempts=list(attempts),expected_exit_codes=attempts,lean_jobs=3,failed_attempts=1,production_pairs=0,constructed_pairs=1,canonical=None,canonical_jobs=0,source_sha256=sha((h/'unfold-kernels.lean').read_bytes()),printer_sha256=sha((h/'unfold-kernels-public.lean').read_bytes()),prior_fixture_sha256='8807b07779bc396921b3d13e235be8c97d3705bc2f9a197172c428b57735e29c'))
(h/'unfold-kernels-review.md').write_text('''# An actual captured Mu unfold retains one source callback

This is a new constructed consumer of the same nested source family. The prior frozen packages stay unchanged. The concrete source, computation, support, and physical admission helpers are byte-identical to the selected row-capture fixture after the namespace/import prefix. The closed source builds two distinct used outer Mu values. Each body contains a closed used inner Mu. The actual checked prefix reaches the outer optional. Its available body leaf pool contains a newly generated full used inner Mu at occurrence one. The exact selected key has no initial record and has its full record at the current heap.

The source build and actual Top allocation derive initial Good. Empty native tables derive initial native History. closed_history supplies the initial source publication History. source_trace supplies the publication History at the actual current heap. No History is inferred from Grows. Existing physical admission checks the actual raw trace.

The fixture computes a successful repaired unfold of that exact captured Mu at the current heap. The selected literal output row is row zero. Its symbol is rec, its guard is the allocated Top constraint, and its child list is the singleton captured Mu. The original stored row's child list is the singleton bare own reference. The output row and stored row differ. The actual stored body has one structural row. A private inversion proves that every returned original stored row is this same computed row.

The witness calls CapturedMuUnfoldRows.capture once. Initial absence excludes its initial-cell arm. The same earlier optional tuple keeps its strict prefix, suffix to the current outer optional, actual maybeMu call, source build, rooted writer, full owner/child/terminal origin, and row-production Cases. It also keeps the Stored receipt. The Observed receipt is expanded in the public type. One event and raw callback are selected before both the stored-row and actual-unfold universal clauses. These clauses retain that same event, raw value, and historical raw build interval.

The proof applies the returned universal clause to the actual successful unfold and actual literal row. It excludes the unchanged-row arm. It therefore obtains actual ordered Calls from the original stored row's children to the output row's children. The same original row has RowAt in the raw callback and SourceRow for the same event expression, lexical inputs, allocated entry heap, raw value, and raw return heap. The source row is not a separately chosen parallel receipt. The public theorem exposes the actual row, changed child, fixed callback, and SourceRow directly. It does not hide the result behind an Observed alias.

The public theorem aliases the checked private witness with an identical complete type. Selected direct-2 is terminal zero with a literal-empty raw log. Selected public-1 is terminal zero with one full statement/proof/axiom group, all eight settings, standard axioms only, and no warnings or omissions. The source is ebbf5c4a6c1dce18a7d9fe6cb9f1ccb21d0d8667c1f96c2cc317273e990110e1. The printer source is f672c597feef1975f4b5dbd83412386bddd8bfbd87333949be5e9764af1d06b9. Three owned Lean commands are preserved. One initial command failed at literal Row constructor inference from nodeEdges membership. A private case split corrects this inference. No source family or claim changed.

All commands use pinned Lean 4.34.1, effective 4 GiB max/high, zero swap, and a five-minute cap with fresh usage receipts. There is one constructed pair, no production pair, and no canonical job. The mutable peaks file is excluded. A dedicated final three-row peaks snapshot is pinned. The portable verifier performs no Lean work.

This is a nonnullary row example. It does not test the nullary alternative or every row-production Cases branch. The leaf index is an occurrence index, not encode.slot. The fixture does not prove source-index equality, optional-site uniqueness, a particular identity for every existential field, original-root binding ancestry, a global rank, arbitrary later owner retention, productivity, finite acceptance, outer completion, or Haskell refinement. The child-call interval is the interval returned by the theorem. It is not asserted equal to the whole unfold interval.
''')
shutil.copyfile(h/'unfold-kernels-peaks.txt',h/'unfold-kernels-peaks-final.txt')
(h/'inputs').mkdir(exist_ok=True)
paths=[x['path'] for x in json.loads((old/'captured-row-kernels-source-pins.json').read_text())['sources']]
paths+=['lean/MicroCFTA/SourceCurrentNativeCapturedMuUnfoldRows.lean','lean/MicroCFTA/SourceCurrentNativeCapturedMuStoredRows.lean','lean/MicroCFTA/SourceCurrentNativePublicationTrace.lean','lean/MicroCFTA/SourceCurrentNativeMuPublication.lean','lean/MicroCFTA/SourceCurrentNativeMuIssuedHistory.lean','lean/MicroCFTA/SourceCurrentNativeMuWriterSourceRows.lean','lean/MicroCFTA/SourceCurrentStoredLiteralRowLineage.lean','lean/MicroCFTA/SourceCurrentPublicationBodySourceRows.lean','lean/MicroCFTA/SourceCurrentStoredSubstitutionCalls.lean']
paths=list(dict.fromkeys(paths));pins=[]
for path in paths:
 data=(root/path).read_bytes();snapshot='inputs/'+Path(path).name;(h/snapshot).write_bytes(data)
 pins.append(dict(path=path,snapshot=snapshot,bytes=len(data),sha256=sha(data)))
(h/'inputs/prior-captured-row-kernels.lean').write_bytes((old/'captured-row-kernels.lean').read_bytes())
write('unfold-kernels-source-pins.json',dict(sources=pins))
files=['unfold-kernels.lean','unfold-kernels-public.lean','unfold-kernels-run-check.py','unfold-kernels-capped-worker.py','prepare_unfold_fixture.py','package_unfold_fixture.py','unfold-kernels-review.md','unfold-kernels-selection.json','unfold-kernels-source-pins.json','unfold-kernels-peaks-final.txt','unfold-kernels-verify.py','inputs/prior-captured-row-kernels.lean']
for stem in attempts:files.extend(stem+suffix for suffix in ['.json','.source.lean','.limits.json','.usage.json','.log'])
entries=[]
for path in files:
 data=(h/path).read_bytes();entries.append(dict(path=path,bytes=len(data),sha256=sha(data)))
write('unfold-kernels-manifest.json',dict(schema=1,files=entries,sources=pins))
