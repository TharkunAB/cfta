from pathlib import Path
import hashlib,json,shutil,datetime
HERE=Path(__file__).resolve().parent
ROOT=Path('/home/tritlo/Code/mcfta')
PREFIX='publication-trace-kernels'
NAME='MicroCFTA.OriginalPublicationTraceFixture.actual_strict_publication_order'
ATTEMPTS={PREFIX+'-direct-1':0,PREFIX+'-public-1':0}
def sha(data):return hashlib.sha256(data).hexdigest()
def write(name,value):
 (HERE/name).write_text(json.dumps(value,indent=2)+'\n')
source=(HERE/(PREFIX+'.lean')).read_bytes()
printer=(HERE/(PREFIX+'-public.lean')).read_bytes()
assert sha(source)=='f6d3b7cd18c99580e7930f11099eab4014f6e61725f969f73db896ffe684e7cf'
assert sha(printer)=='b18623e71434a2cf847869e098d7ff7990ab57f2f9458d4d7aa753c4ff81794e'
assert not (HERE/(PREFIX+'-direct-1.log')).read_bytes()
shutil.copyfile(HERE/(PREFIX+'-peaks.txt'),HERE/(PREFIX+'-peaks-final.txt'))
(HERE/'inputs').mkdir(exist_ok=True)
shutil.copyfile('/tmp/mcfta-native-original-observed-resume-fixture/observed-resume-kernels.lean',HERE/'inputs/prior-observed-resume-kernels.lean')
modules=['SourceCurrentNativeOriginalPublicationTrace','SourceCurrentBuildStructuralRowOrigins','SourceCurrentNativeMuPublicationCallbacks','SourceCurrentNativePublicationRawSuffix','SourceEqualityPCSNativeEdge','SourceEqualityNormalizationReceipt','InternedFreshOrdinaryFacts','InternedFreshOrdinaryConstruction','SourceCurrentConstrainedCapSourceHistory','SourceCurrentNativeMuPublication','SourceCurrentNativeMuIssuedHistory','InternedFreshOrdinarySourceHistory','InternedConstructionProvenance','SourceCurrentStoredLiteralRowLineage','InternedProbeProvenance','InternedConstructorTemplates']
sources=[]
for rel in ['lean/MicroCFTA/'+name+'.lean' for name in modules]+['lean/lean-toolchain']:
 data=(ROOT/rel).read_bytes();snap='inputs/'+Path(rel).name
 (HERE/snap).write_bytes(data)
 sources.append(dict(path=rel,snapshot=snap,bytes=len(data),sha256=sha(data)))
assert sources[0]['sha256']=='4269eff77ca39081f7ef89829cee433e4255459acf1b0419f0053dcd3885ddf4'
write(PREFIX+'-source-pins.json',dict(schema='portable-source-pins-v1',sources=sources))
write(PREFIX+'-selection.json',dict(schema='constructed-fixture-selection-v1',finalized=True,source=PREFIX+'.lean',source_sha256=sha(source),printer_sha256=sha(printer),strict=PREFIX+'-direct-1',groups=[dict(name=PREFIX+'-public-1',pairs=1,kind='constructed',full_proof=True)],public_heads=[NAME],attempts=list(ATTEMPTS),expected_exit_codes=ATTEMPTS,lean_jobs=2,failed_attempts=0,production_pairs=0,constructed_pairs=1,canonical=None,canonical_jobs=0,distinct_new_source_examples=0,source_data_helpers_byte_identical=True))
(HERE/(PREFIX+'-review.md')).write_text('''# Shared actual publication order fixture

Reviewed at 2026-10-20 23:02 CEST.

The source family is the prior warm source family. Its first box child builds a raw nullary tagged Mu. Its second child builds a raw outer Mu. The outer body is `union[var0,nested]`. The nested request reuses the first full payload. This component adds one constructed theorem. It adds no production theorem, canonical build, or new source family.

The proof calls `build_trace_writers` once on the actual completed closed source build. It retains that producer's one issued `Path`, all indexed source roots, final writers, and precompletion writers. It selects a final outer full cell on that same path. Full candidate equality identifies its stored body with the inner Mu. The actual callback context and `callback_verified` derive `Available` at that recovered outer event's `afterBody`. `Available.resident` then supplies the exact inner full cell there. The precompletion clause consumes that same outer lookup and inner cell. The result contains explicit events and indices `i < j` in the same path. Both full payloads, rooted source receipts, callback intervals, missing-before-publication facts, growth, and issued suffixes remain in the public type.

The proof does not equate the recovered events with the manually constructed setup event. It does not choose numeric event indices or prove event uniqueness. The strict order is publication completion order. It is not a source binding rank, native query result, general ancestry measure, termination theorem, or Haskell refinement claim. The source uses raw binders. It does not assert a used recursive child.

The data and actual source-call helpers are byte-identical to the frozen observed-resume fixture, after namespace and import changes. The new callback availability and order proof follows those helpers. The public theorem aliases a private checked proof with an identical expanded type.

Two owned Lean jobs ran. Both passed on the first attempt. The selected strict log has zero bytes. The full public group prints one `#check @`, one full `#print`, and one `#print axioms`. All eight print/linter settings are enabled. The 1,155,998-byte full log has no omissions or printer failures. Its axioms are only `propext`, `Classical.choice`, and `Quot.sound`. Each job uses pinned Lean 4.34.1, a fresh usage receipt, a five-minute cap, memory max/high 4 GiB, and zero swap. No own jobs remain live. Mutable peaks are excluded; the final two-row snapshot is pinned.

The standalone verifier uses local source snapshots by default. `--live --root ROOT` also checks the current repository source bytes. Raw commands and receipts retain their original temporary paths. The package does not modify any prior source, fixture, or evidence package.
''')
print(json.dumps(dict(source=sha(source),printer=sha(printer),sources=len(sources))))
