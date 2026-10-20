from pathlib import Path
import datetime, hashlib, json, shutil
here=Path('/tmp/mcfta-native-consistent-owner-fixture')
root=Path('/home/tritlo/Code/mcfta')
def write(name,obj): (here/name).write_text(json.dumps(obj,indent=2)+'\n')
name='MicroCFTA.NativeConsistentOwnerFixture.actual_consistent_site'
write('consistent-kernels-selection.json',dict(finalized=True,public_heads=[name],strict='consistent-kernels-direct-4',groups=[dict(name='consistent-kernels-public-1',pairs=1,kind='constructed',full_proof=True)],attempts=['consistent-kernels-direct-1','consistent-kernels-direct-2','consistent-kernels-direct-3','consistent-kernels-direct-4','consistent-kernels-public-1'],lean_jobs=5,failed_attempts=3,production_pairs=0,constructed_pairs=1,canonical=None,canonical_jobs=0,source_sha256='29f2c021b8b95e9ff1926eaf2514e163c849ea43ecf3326823d96c2ce262639b'))
(here/'consistent-kernels-review.md').write_text('''# Actual consistent owner and child writer

The actual source builds produce two distinct raw Mu values. The first has an Empty body. The second has one nullary leaf row. The fixture allocates the Top equality field with `emptyField empty` before construction. Source preservation proves the exact heap Ready. Annotation preservation proves all stored fields loaded. These facts derive initial `Good`. Empty native memo tables derive the native `History.initial`. Actual source execution also derives physical publication history.

The four checked transitions perform the root query, enter its domain, execute the keyed Empty/leaf child query, and finish that child. The selected state contains the root owner in `evaluating` and the child in `returned Empty`. The optional instruction has not executed. The owner has not returned.

The fixture calls `OptionalChildOrigin.request` once. It unpacks that result once. Its final evaluating cell and the computed cell inventory identify the queried request. The same entered-child request is keyable. This excludes the direct arm of its returned `Forwarded` receipt. The returned existential therefore retains the same owner, site, child interval, returned child cell, and strong child writer. No separate internal History or desired writer is supplied.

The sole public theorem is an alias of the checked private witness. Its complete statement remains explicit. Both source build equations, the actual Trace, all initial evidence, the full raw owner tuple, and the same child writer appear in that statement.

This fixture exercises a returned child writer. Its local result is Empty. It does not exercise new Mu generation, an owner return, an arbitrary later reader, original source binding ancestry, or outer termination. The two raw binders are unused. There is no false-primary gate claim.

Selected strict: `consistent-kernels-direct-4`, terminal 0 with a literal zero-byte log. Selected full pair: `consistent-kernels-public-1`, terminal 0, all eight printer/linter settings, complete proof, standard three axioms only. Five unique Lean commands are preserved. The first three failed during elaboration: missing inferred parameters/notations and a finite-table proof. The fourth strict command and the public command passed. No canonical job is owned. Every command used pinned Lean 4.34.1 under effective 4 GiB max/high, zero swap, and a five-minute cap. Each command has a fresh usage receipt.

`prepare_fixture.py` is an unselected draft generator. The final source is `consistent-kernels.lean`. Frozen attempt sources preserve the exact checked inputs. The mutable peaks file is excluded. A dedicated final peaks snapshot is pinned. The verifier performs no Lean execution.
''')
shutil.copyfile(here/'consistent-kernels-peaks.txt',here/'consistent-kernels-peaks-final.txt')
source_names=['SourceCurrentNativeOptionalChildOrigin','SourceCurrentNativeConsistentOptionalOwner','SourceCurrentNativeOwnerSiteRetention','SourceCurrentNativePrefixWriterMaps','SourceCurrentNativeForwardLineage','SourceCurrentNativeWriterReadyRetention','SourceCurrentNativeEdgeWriterGrowth','SourceCurrentAllocatedNativePhysicalCompletion','SourceCurrentAllocatedNativePhysicalCache','SourceCurrentConjunctionFieldAllocation','SourceEqualityAnnotationConstruction','SourceEqualityRequiredCache','InternedOpenDepthExecution','InternedFreshOrdinaryCoverage','SourceCurrentNativeMuPublication','SourceCurrentConstrainedCapSourceHistory']
inputs=here/'inputs';inputs.mkdir(exist_ok=True)
sources=[]
for n in source_names:
 rel='lean/MicroCFTA/'+n+'.lean';data=(root/rel).read_bytes();snap='inputs/'+n+'.lean';(here/snap).write_bytes(data)
 sources.append(dict(path=rel,snapshot=snap,bytes=len(data),sha256=hashlib.sha256(data).hexdigest()))
for rel,snap in [('lean/lean-toolchain','inputs/lean-toolchain'),('lean/restart-evidence/20261020-native-optional-owner-prefix/compiled-owner-fixture/owner-kernels.lean','inputs/prior-owner-kernels.lean')]:
 data=(root/rel).read_bytes();(here/snap).write_bytes(data);sources.append(dict(path=rel,snapshot=snap,bytes=len(data),sha256=hashlib.sha256(data).hexdigest()))
write('consistent-kernels-source-pins.json',dict(sources=sources))
