from pathlib import Path
import hashlib,json,shutil
h=Path(__file__).resolve().parent
root=Path('/home/tritlo/Code/mcfta')
old=Path('/tmp/mcfta-native-captured-stored-unfold-fixture')
def sha(data):return hashlib.sha256(data).hexdigest()
def write(name,obj):(h/name).write_text(json.dumps(obj,indent=2)+'\n')
attempts={'original-kernels-direct-1':1,'original-kernels-direct-2':0,'original-kernels-public-1':0}
write('original-kernels-selection.json',dict(finalized=True,public_heads=['MicroCFTA.OriginalCapturedMuFixture.actual_initial_capture'],strict='original-kernels-direct-2',groups=[dict(name='original-kernels-public-1',pairs=1,kind='constructed',full_proof=True)],attempts=list(attempts),expected_exit_codes=attempts,lean_jobs=3,failed_attempts=1,production_pairs=0,constructed_pairs=1,canonical=None,canonical_jobs=0,source_sha256=sha((h/'original-kernels.lean').read_bytes()),printer_sha256=sha((h/'original-kernels-public.lean').read_bytes()),prior_fixture_sha256='ebbf5c4a6c1dce18a7d9fe6cb9f1ccb21d0d8667c1f96c2cc317273e990110e1'))
(h/'original-kernels-review.md').write_text('''# An actual initial Mu capture retains its original source callback

This source family differs from the previous generated-inner example. Both distinct closed used outer Mu operands now contain the same closed used inner Mu. Their outer nullary labels still differ. Their inner nullary label is sharedInner. The fixture computes the same full inner Mu at child one of each actual outer stored row. The actual native prefix reaches the outer optional and captures this inner Mu at leaf occurrence one. Its exact full record is present both in the initial source heap and at the current heap. The source build and actual Top allocation derive initial Good. Empty native tables derive initial native History. Existing source admission checks the actual raw trace.

The witness calls OriginalCapturedMuRows.capture_source once with that completed original source build. It unpacks the result once. The generated alternative would have an earlier site with no record at the captured key. The proof transports the actual initial full record through that alternative's same prefixGrowth. This contradicts its None field. The proof therefore forces the initial alternative. It retains that returned initial full-cell receipt and the original program's Observed receipt. It does not assume the initial alternative or choose a second writer.

The public type expands the original-root Observed receipt. One event and raw callback are selected before the stored-row and unfold universal clauses. Their Reached fields use the actual original source expression and empty initial capture list. They do not use the generated encode root. The fixed event retains its full Mu payload, missing-before-publication record, issued paths, physical suffix to the initial heap, actual raw callback build/filter, rich Context, and original-root callback Reached receipt. Every stored or actual observed row uses that same event and raw callback.

The captured initial Mu has both its recursive row and its nullary tag row. The fixture selects the actual rec row by its computed canonical index. It does not assume the previous single-row stored shape. A private filtered-membership proof identifies the returned original row by its rec symbol. The actual repaired unfold at the current heap succeeds. Its rec/Top row has the singleton full captured Mu child. The original stored rec row has the singleton bare own reference. The rows differ. This excludes the unchanged-row arm and yields actual ordered Calls from the original children to the output children. The same original stored row has RowAt in the fixed raw callback and SourceRow for that same callback interval.

The source data and resource proof change only to share the inner syntax, retain an initial Some record, and use the checked smaller initial node count. The verifier compares the remaining data/admission block with the prior frozen fixture after these explicit changes. This is not a claim of whole-block byte identity. The public theorem aliases its checked private witness with an identical complete type. It exposes the original source callback and concrete changed-child Calls directly, without hiding them behind an Observed alias.

Three owned capped Lean commands are preserved. The first fails at a definitional nodeEdges/filter rewrite in the private rec-row uniqueness helper. The correction changes only that rewrite. Selected direct-2 has a literal-empty raw log. Selected public-1 has one full statement/proof/axiom group, all eight settings, standard axioms only, and no warnings or omissions. There is one constructed pair, no production pair, and no canonical job. All commands use pinned Lean 4.34.1, effective 4 GiB max/high, zero swap, and a five-minute cap with fresh usage receipts. The mutable peaks file is excluded. A dedicated final three-row snapshot is pinned. The portable verifier performs no Lean work.

The leaf index is an occurrence index. It is not encode.slot or an original syntax index. The fixture does not identify a unique source binder occurrence or prove global ancestry for optional-generated captures. It does not test every row-production alternative or the nullary unfold row. It does not prove a global rank, arbitrary later owner retention, productivity, finite acceptance, outer completion, or Haskell refinement. The child-call interval is the returned interval. It is not asserted equal to the whole unfold interval.
''')
shutil.copyfile(h/'original-kernels-peaks.txt',h/'original-kernels-peaks-final.txt')
(h/'inputs').mkdir(exist_ok=True)
paths=[x['path'] for x in json.loads((old/'unfold-kernels-source-pins.json').read_text())['sources']]
paths+=['lean/MicroCFTA/SourceCurrentNativeRootedMuStoredRows.lean','lean/MicroCFTA/SourceCurrentNativeOriginalCapturedMuRows.lean']
paths=list(dict.fromkeys(paths));pins=[]
for path in paths:
 data=(root/path).read_bytes();snapshot='inputs/'+Path(path).name;(h/snapshot).write_bytes(data)
 pins.append(dict(path=path,snapshot=snapshot,bytes=len(data),sha256=sha(data)))
(h/'inputs/prior-unfold-kernels.lean').write_bytes((old/'unfold-kernels.lean').read_bytes())
write('original-kernels-source-pins.json',dict(sources=pins))
files=['original-kernels.lean','original-kernels-public.lean','original-kernels-run-check.py','original-kernels-capped-worker.py','prepare_original_fixture.py','prepare_original_consumer.py','package_original_fixture.py','original-kernels-review.md','original-kernels-selection.json','original-kernels-source-pins.json','original-kernels-peaks-final.txt','original-kernels-verify.py','inputs/prior-unfold-kernels.lean']
for stem in attempts:files.extend(stem+suffix for suffix in ['.json','.source.lean','.limits.json','.usage.json','.log'])
entries=[]
for path in files:
 data=(h/path).read_bytes();entries.append(dict(path=path,bytes=len(data),sha256=sha(data)))
write('original-kernels-manifest.json',dict(schema=1,files=entries,sources=pins))
