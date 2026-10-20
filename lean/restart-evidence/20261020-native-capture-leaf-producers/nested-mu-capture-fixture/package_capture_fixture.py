from pathlib import Path
import hashlib,json,shutil
h=Path(__file__).resolve().parent
root=Path('/home/tritlo/Code/mcfta')
old=Path('/tmp/mcfta-native-compiled-terminal-generation-fixture')
def sha(data):return hashlib.sha256(data).hexdigest()
def write(name,obj):(h/name).write_text(json.dumps(obj,indent=2)+'\n')
attempts={'captured-mu-calculation-1':1,'captured-mu-calculation-2':124,'captured-mu-locator-1':1,'captured-mu-locator-2':0,'captured-mu-calculation-3':0,'captured-mu-kernels-direct-1':1,'captured-mu-kernels-direct-2':0,'captured-mu-kernels-public-1':0}
write('captured-mu-kernels-selection.json',dict(finalized=True,public_heads=['MicroCFTA.NestedCapturedMuFixture.actual_nested_capture'],strict='captured-mu-kernels-direct-2',groups=[dict(name='captured-mu-kernels-public-1',pairs=1,kind='constructed',full_proof=True)],attempts=list(attempts),expected_exit_codes=attempts,lean_jobs=8,failed_attempts=4,timeout_attempts=1,production_pairs=0,constructed_pairs=1,canonical=None,canonical_jobs=0,source_sha256=sha((h/'captured-mu-kernels.lean').read_bytes()),printer_sha256=sha((h/'captured-mu-kernels-public.lean').read_bytes())))
(h/'captured-mu-kernels-review.md').write_text('''# An actual outer optional captures an earlier generated Mu

The concrete source builds two distinct closed used outer Mu values. Each outer body has a recursive `outer[self,inner]` row and a distinct nullary row. Each closed inner Mu has a recursive `rec[self]` row and its own distinct nullary row. All guards use the actual allocated Top field. The closed source build derives the physical source facts, semantic readiness, availability, and initial Good state. The empty native tables derive the initial native History.

The checked raw execution stops at the outer pair's actual optional instruction. Its available body contains a new full used inner Mu at leaf occurrence index one. The initial source record at that exact key is absent. The current record is present. The fixture computes both facts from the actual source and execution. The leaf pool also contains the outer intersection reference. The leaf occurrence is not an encode.slot or a source-syntax child index.

The witness calls CapturedMuOrigins.capture once. The initial absence rules out its initial-cell arm. It retains the same returned earlier generating optional site, its strict prefix fuel and actual suffix to the outer optional, the maybeMu call, the exact compiled source build and rooted Written receipt, and the physical and issued growth facts. The same existential also contains the full owner, entered-child, terminal Route, exact returned terminal cell, strong terminal writer, and distinct terminal/owner handles. The fixture does not choose a parallel event or writer. It does not assume a desired generation, owner, source result, or internal History.

The public theorem is an alias to the checked private witness. Their complete types are identical. The public type expands the earlier OptionalTerminalOrigin tuple. It does not hide that tuple behind the Origin predicate.

Eight capped Lean commands are preserved. Four fail: an initial reserved identifier, a five-minute calculation timeout, a continuation-function equality calculation, and a direct consumer check whose three numeric resource computations exceeded maxRecDepth. The timeout is not evidence of a semantic defect. The working locator uses a direct Boolean match and a generic outcome-tag reconstruction. The final resource proof uses checked small initial counters and power monotonicity. These changes preserve the actual fixture and the full claim. The selected direct-2 raw log is literally empty. The selected public-1 log contains one complete full statement/proof/axiom group with all eight settings, standard axioms only, and no warnings or omissions. The selected source is 77213d610a4bf32891c3d721c78dc9cfc1946c0b6a111ec61ae45a945cc4b85a. The public printer source is bb4e2552490afdc573048f0801d8663cf458409113a865502e8d1827769be363.

Every command uses pinned Lean 4.34.1, effective 4 GiB max/high, zero swap, and a five-minute cap. Fresh usage receipts are preserved. The mutable peaks file is excluded. A dedicated final eight-row peaks snapshot is pinned. There is one constructed proof pair, no production pair, and no canonical job. The portable verifier performs no Lean work.

This example proves actual earlier generation and capture at the outer optional. It does not prove optional-site uniqueness, encode-slot equality, original-root binding ancestry, arbitrary later owner retention, productivity, finite acceptance, outer completion, or Haskell refinement. It does not claim every existential field equals a selected literal constant. It does not test the later row-production strengthening.
''')
shutil.copyfile(h/'captured-mu-kernels-peaks.txt',h/'captured-mu-kernels-peaks-final.txt')
(h/'inputs').mkdir(exist_ok=True)
paths=[x['path'] for x in json.loads((old/'terminal-mu-kernels-source-pins.json').read_text())['sources'] if not x['path'].endswith('/SourceCurrentNativeTerminalGeneration.lean')]
paths+=['lean/MicroCFTA/SourceCurrentNativeCapturedMuOrigins.lean','lean/MicroCFTA/SourceCurrentNativeMuOptionalGeneration.lean','lean/MicroCFTA/InternedStoredSubstitution.lean','lean/MicroCFTA/SourceCurrentAllocatedRecursiveInitialRanges.lean','lean/MicroCFTA/InternedFreshOrdinaryConstruction.lean','lean/MicroCFTA/SourceCurrentCompletedBuildRootedWriters.lean']
paths=list(dict.fromkeys(paths))
pins=[]
for path in paths:
 data=(root/path).read_bytes();snapshot='inputs/'+Path(path).name;(h/snapshot).write_bytes(data)
 pins.append(dict(path=path,snapshot=snapshot,bytes=len(data),sha256=sha(data)))
write('captured-mu-kernels-source-pins.json',dict(sources=pins))
files=['captured-mu-kernels.lean','captured-mu-kernels-public.lean','captured-mu-calculation.lean','captured-mu-locator.lean','captured-mu-kernels-run-check.py','captured-mu-kernels-capped-worker.py','prepare_capture_fixture.py','prepare_capture_consumer.py','package_capture_fixture.py','captured-mu-kernels-review.md','captured-mu-kernels-selection.json','captured-mu-kernels-source-pins.json','captured-mu-kernels-peaks-final.txt','captured-mu-kernels-verify.py']
for stem in attempts:
 files.extend(stem+suffix for suffix in ['.json','.source.lean','.limits.json','.usage.json','.log'])
entries=[]
for path in files:
 data=(h/path).read_bytes();entries.append(dict(path=path,bytes=len(data),sha256=sha(data)))
write('captured-mu-kernels-manifest.json',dict(schema=1,files=entries,sources=pins))
