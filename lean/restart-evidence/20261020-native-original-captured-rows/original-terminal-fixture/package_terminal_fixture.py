from pathlib import Path
import hashlib,json,shutil
h=Path(__file__).resolve().parent
root=Path('/home/tritlo/Code/mcfta')
old=Path('/tmp/mcfta-native-original-captured-fixture')
def sha(data):return hashlib.sha256(data).hexdigest()
def write(name,obj):(h/name).write_text(json.dumps(obj,indent=2)+'\n')
attempts={'terminal-kernels-direct-1':1,'terminal-kernels-direct-2':0,'terminal-kernels-public-1':0}
write('terminal-kernels-selection.json',dict(finalized=True,public_heads=['MicroCFTA.OriginalCapturedTerminalFixture.actual_initial_terminal'],strict='terminal-kernels-direct-2',groups=[dict(name='terminal-kernels-public-1',pairs=1,kind='constructed',full_proof=True)],attempts=list(attempts),expected_exit_codes=attempts,lean_jobs=3,failed_attempts=1,production_pairs=0,constructed_pairs=1,canonical=None,canonical_jobs=0,source_sha256=sha((h/'terminal-kernels.lean').read_bytes()),printer_sha256=sha((h/'terminal-kernels-public.lean').read_bytes()),prior_fixture_sha256='563d380c1b80af6bc8a04c6683d6e651e8349f5e1f83f61aea97c5ec0f3e21fe',distinct_new_source_examples=0))
(h/'terminal-kernels-review.md').write_text('''# The same initial capture retains original source terminals

This is a stronger proof of the same shared-inner actual source family. It is one example across the original-capture and terminal proof versions. The prior package remains unchanged. The complete data, source, computation, support, resource, physical admission, shared-capture, and actual unfold helper block is byte-identical to that prior selected source after the namespace/import prefix.

Both distinct closed used outer Mu operands contain the same closed used inner Mu. The actual outer optional captures that initial inner Mu at leaf occurrence one. Actual source construction and Top allocation derive Good. Empty native tables derive native History. The checked native prefix and actual initial full record are derived. The witness calls capture_source once. Its generated arm is excluded by transporting the actual initial record through that same alternative's prefixGrowth and contradicting its absent-site record. The initial alternative is not assumed.

The proof applies OriginalObservedTerminals.of_observed once, before unpacking the returned initial Observed receipt. The enriched receipt fixes one event and raw callback before both the stored-row and actual-unfold universal clauses. It retains the same original root, empty initial capture list, actual raw source build/filter, rich Context, payload and physical/issued intervals. Each stored row and each original stored row selected by a successful actual unfold now has Terminal under that same event expression and raw return heap.

The actual rec/Top row has a full captured Mu child. Its original stored row has a bare own-reference child. The rows differ, so the proof obtains actual ordered Calls. The same returned original row has RowAt in the fixed raw callback, SourceRow at that callback, and Terminal for that same event expression and raw return heap. The public type exposes all three Terminal clauses explicitly: the stored-row universal clause, the actual-unfold universal clause, and the concrete rec original-row clause. It does not choose a separate event, callback, terminal, or row.

Terminal retains an actual completed terminal source build, a node-or-binder syntax alternative, nonunion syntax, Context, original-root Reached, a generic source-syntax size bound, and physical and issued suffixes to the same raw callback return. Its exact public predicate is used in the fixture. The first strict attempt copied its textual sizeOf field into the concrete fixture type. This selected a different concrete SizeOf instance and failed type checking. The final proof retains the exact public Terminal predicate and its original generic measure. This is an integration type mismatch, not a defect in the producer or native execution.

The selected public theorem aliases its checked private witness with an identical complete type. Selected direct-2 has a literal-empty raw log. Selected public-1 has one full statement/proof/axiom group, all eight settings, standard axioms only, and no warnings or omissions. There are three preserved capped Lean commands, one failed integration attempt, no production pair, one constructed pair, and no canonical job. All commands use pinned Lean 4.34.1, effective 4 GiB max/high, zero swap, and a five-minute cap with fresh usage receipts. The mutable peaks file is excluded. A dedicated final three-row peaks snapshot is pinned. The portable verifier performs no Lean work.

This fixture does not equate the leaf occurrence with encode.slot or a source syntax index. It does not identify a unique source binder or all existential terminal fields with chosen constants. The terminal source-size relation is not a strict returned-value rank. The fixture does not prove original-root ancestry for arbitrary optional-generated captures, global renewal, arbitrary later owner retention, productivity, finite acceptance, outer completion, or Haskell refinement. It exercises the nonnullary rec row, not every row-production alternative. The child-call interval is not asserted equal to the whole unfold interval.
''')
shutil.copyfile(h/'terminal-kernels-peaks.txt',h/'terminal-kernels-peaks-final.txt')
(h/'inputs').mkdir(exist_ok=True)
paths=[x['path'] for x in json.loads((old/'original-kernels-source-pins.json').read_text())['sources']]
paths+=['lean/MicroCFTA/SourceCurrentNativeOriginalObservedTerminals.lean','lean/MicroCFTA/SourceCurrentNativeOriginalRowTerminals.lean','lean/MicroCFTA/SourceCurrentSourceRowTerminalSuffix.lean','lean/MicroCFTA/SourceCurrentSourceCaptureOriginalSlots.lean']
paths=list(dict.fromkeys(paths));pins=[]
for path in paths:
 data=(root/path).read_bytes();snapshot='inputs/'+Path(path).name;(h/snapshot).write_bytes(data)
 pins.append(dict(path=path,snapshot=snapshot,bytes=len(data),sha256=sha(data)))
(h/'inputs/prior-original-kernels.lean').write_bytes((old/'original-kernels.lean').read_bytes())
write('terminal-kernels-source-pins.json',dict(sources=pins))
files=['terminal-kernels.lean','terminal-kernels-public.lean','terminal-kernels-run-check.py','terminal-kernels-capped-worker.py','prepare_terminal_fixture.py','package_terminal_fixture.py','terminal-kernels-review.md','terminal-kernels-selection.json','terminal-kernels-source-pins.json','terminal-kernels-peaks-final.txt','terminal-kernels-verify.py','inputs/prior-original-kernels.lean']
for stem in attempts:files.extend(stem+suffix for suffix in ['.json','.source.lean','.limits.json','.usage.json','.log'])
entries=[]
for path in files:
 data=(h/path).read_bytes();entries.append(dict(path=path,bytes=len(data),sha256=sha(data)))
write('terminal-kernels-manifest.json',dict(schema=1,files=entries,sources=pins))
