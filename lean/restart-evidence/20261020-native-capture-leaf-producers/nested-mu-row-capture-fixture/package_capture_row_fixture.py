from pathlib import Path
import hashlib,json,shutil
h=Path(__file__).resolve().parent
root=Path('/home/tritlo/Code/mcfta')
old=Path('/tmp/mcfta-native-nested-mu-capture-fixture')
def sha(data):return hashlib.sha256(data).hexdigest()
def write(name,obj):(h/name).write_text(json.dumps(obj,indent=2)+'\n')
attempts={'captured-row-kernels-direct-1':0,'captured-row-kernels-public-1':0}
write('captured-row-kernels-selection.json',dict(finalized=True,public_heads=['MicroCFTA.NestedCapturedMuRowFixture.actual_nested_row_capture'],strict='captured-row-kernels-direct-1',groups=[dict(name='captured-row-kernels-public-1',pairs=1,kind='constructed',full_proof=True)],attempts=list(attempts),expected_exit_codes=attempts,lean_jobs=2,failed_attempts=0,production_pairs=0,constructed_pairs=1,canonical=None,canonical_jobs=0,source_sha256=sha((h/'captured-row-kernels.lean').read_bytes()),printer_sha256=sha((h/'captured-row-kernels-public.lean').read_bytes()),prior_fixture_sha256='77213d610a4bf32891c3d721c78dc9cfc1946c0b6a111ec61ae45a945cc4b85a'))
(h/'captured-row-kernels-review.md').write_text('''# The same captured Mu retains its earlier raw row producers

This is a separate strengthened proof of the same actual nested source family. The original capture package remains unchanged. The data, computation, source support, and physical admission helpers are byte-identical to its selected source after the namespace/import prefix. The new source replaces its single capture call with CapturedMuRowProduction.capture. It makes no second capture or owner call.

The actual closed source builds two distinct used outer Mu values. Each body contains a used recursive inner Mu. Actual execution reaches the outer optional. Its available body leaf pool contains a new full used inner Mu at occurrence one. The exact key has no initial record and has its full record at the current heap. Top allocation and the source build derive initial Good. Empty native tables derive initial native History. The existing physical admission theorem checks the actual raw trace. No desired generation, owner, row origin, or internal History premise is supplied.

The initial absence excludes the initial-cell arm. The same returned earlier optional producer retains its strict earlier prefix, actual suffix to the current outer optional, maybeMu call, source build, rooted writer, and physical and issued growth. Its expanded owner, entered-child, and terminal tuple is retained. The final universal conjunct states that every selected raw nodeEdges row of that same earlier parent has ActiveRowProduction.Cases at that same reader, terminal request, and terminal handle. The proof does not choose a second terminal writer. The public type exposes this universal conjunct explicitly.

One actual nested family exercises the new producer. It does not test each alternative in the exhaustive Cases definition. It does not equate the leaf occurrence with encode.slot. It does not prove site uniqueness, original-root binding ancestry, arbitrary later owner retention, productivity, finite acceptance, outer completion, or Haskell refinement.

The public theorem aliases its checked private witness with an identical complete type. The selected strict direct-1 has a literal-empty raw log. The selected public-1 has one full statement/proof/axiom group with all eight required settings, standard axioms only, and no warnings or omissions. There are two owned Lean commands, no failures, no production pair, one constructed pair, and no canonical job. Both commands use pinned Lean 4.34.1, effective 4 GiB max/high, zero swap, and a five-minute cap with fresh usage receipts. The mutable peaks file is excluded. A dedicated final two-row peaks snapshot is pinned. The portable verifier performs no Lean work.
''')
shutil.copyfile(h/'captured-row-kernels-peaks.txt',h/'captured-row-kernels-peaks-final.txt')
(h/'inputs').mkdir(exist_ok=True)
paths=[x['path'] for x in json.loads((old/'captured-mu-kernels-source-pins.json').read_text())['sources'] if not x['path'].endswith('/SourceCurrentNativeCapturedMuOrigins.lean')]
paths+=['lean/MicroCFTA/SourceCurrentNativeCapturedMuRowProduction.lean','lean/MicroCFTA/SourceCurrentNativeOptionalRowProduction.lean','lean/MicroCFTA/SourceCurrentNativeActiveRowProduction.lean','lean/MicroCFTA/SourceCurrentNativeActivePairedRows.lean','lean/MicroCFTA/SourceCurrentNativeActiveUnionRowOrigins.lean','lean/MicroCFTA/SourceCurrentNativeActiveReferenceOrigins.lean','lean/MicroCFTA/SourceCurrentNativeActiveMuBodyOrigins.lean']
paths=list(dict.fromkeys(paths));pins=[]
for path in paths:
 data=(root/path).read_bytes();snapshot='inputs/'+Path(path).name;(h/snapshot).write_bytes(data)
 pins.append(dict(path=path,snapshot=snapshot,bytes=len(data),sha256=sha(data)))
(h/'inputs/prior-captured-mu-kernels.lean').write_bytes((old/'captured-mu-kernels.lean').read_bytes())
write('captured-row-kernels-source-pins.json',dict(sources=pins))
files=['captured-row-kernels.lean','captured-row-kernels-public.lean','captured-row-kernels-run-check.py','captured-row-kernels-capped-worker.py','package_capture_row_fixture.py','captured-row-kernels-review.md','captured-row-kernels-selection.json','captured-row-kernels-source-pins.json','captured-row-kernels-peaks-final.txt','captured-row-kernels-verify.py','inputs/prior-captured-mu-kernels.lean']
for stem in attempts:files.extend(stem+suffix for suffix in ['.json','.source.lean','.limits.json','.usage.json','.log'])
entries=[]
for path in files:
 data=(h/path).read_bytes();entries.append(dict(path=path,bytes=len(data),sha256=sha(data)))
write('captured-row-kernels-manifest.json',dict(schema=1,files=entries,sources=pins))
