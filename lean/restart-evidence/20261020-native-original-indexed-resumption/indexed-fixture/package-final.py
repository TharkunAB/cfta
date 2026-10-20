from pathlib import Path
import hashlib,json,shutil
HERE=Path(__file__).resolve().parent
ROOT=Path('/home/tritlo/Code/mcfta')
PREFIX='indexed-resumption-kernels'
NAME='MicroCFTA.OriginalIndexedResumptionFixture.actual_indexed_binder_resumption'
ATTEMPTS={PREFIX+'-direct-1':1,PREFIX+'-direct-2':0,PREFIX+'-public-1':0}
def sha(data):return hashlib.sha256(data).hexdigest()
def write(name,value):(HERE/name).write_text(json.dumps(value,indent=2)+'\n')
source=(HERE/(PREFIX+'.lean')).read_bytes();printer=(HERE/(PREFIX+'-public.lean')).read_bytes()
assert sha(source)=='d1e37939d0fe8e9b7ae0924665a08341ac7a195cd9e861764c04f9835c832818'
assert sha(printer)=='02932156e8189e5faad5dd107fb240657ac4851249c6c16a8c2b0d5b4e168aa4'
assert not (HERE/(PREFIX+'-direct-2.log')).read_bytes()
shutil.copyfile(HERE/(PREFIX+'-peaks.txt'),HERE/(PREFIX+'-peaks-final.txt'))
(HERE/'inputs').mkdir(exist_ok=True)
shutil.copyfile('/tmp/mcfta-native-original-union-descent-fixture/union-descent-kernels.lean',HERE/'inputs/prior-union-descent-kernels.lean')
modules=['SourceCurrentNativeOriginalIndexedResumption','SourceCurrentNativeOriginalPublicationTrace','SourceCurrentNativeOriginalUnionDescent','SourceCurrentNativeOriginalObservedResume','SourceCurrentPublicationBodySourceRows','SourceCurrentBuildStructuralRowOrigins','SourceCurrentNativeMuPublicationCallbacks','SourceCurrentNativePublicationRawSuffix','SourceEqualityPCSNativeEdge','SourceEqualityNormalizationReceipt','InternedFreshOrdinaryFacts','InternedFreshOrdinaryConstruction','SourceCurrentConstrainedCapSourceHistory','SourceCurrentNativeMuPublication','SourceCurrentNativeMuIssuedHistory','InternedFreshOrdinarySourceHistory','InternedConstructionProvenance','SourceCurrentStoredLiteralRowLineage','SourceCurrentStoredMuRetainedAlignment','InternedProbeProvenance','InternedConstructorTemplates']
sources=[]
for rel in ['lean/MicroCFTA/'+name+'.lean' for name in modules]+['lean/lean-toolchain']:
 data=(ROOT/rel).read_bytes();snap='inputs/'+Path(rel).name
 (HERE/snap).write_bytes(data)
 sources.append(dict(path=rel,snapshot=snap,bytes=len(data),sha256=sha(data)))
assert sources[0]['sha256']=='25a3d3a9bc737a7cba638e3ae57b80394e0a761c953b94544e90062f03aaeae3'
write(PREFIX+'-source-pins.json',dict(schema='portable-source-pins-v1',sources=sources))
write(PREFIX+'-selection.json',dict(schema='constructed-fixture-selection-v1',finalized=True,source=PREFIX+'.lean',source_sha256=sha(source),printer_sha256=sha(printer),strict=PREFIX+'-direct-2',groups=[dict(name=PREFIX+'-public-1',pairs=1,kind='constructed',full_proof=True)],public_heads=[NAME],attempts=list(ATTEMPTS),expected_exit_codes=ATTEMPTS,lean_jobs=3,failed_attempts=1,production_pairs=0,constructed_pairs=1,canonical=None,canonical_jobs=0,distinct_new_source_examples=0,source_data_helpers_byte_identical=True,source_forcing_helpers_byte_identical=True))
(HERE/(PREFIX+'-review.md')).write_text('''# Indexed actual binder resumption fixture

Reviewed at 2026-10-20 23:13 CEST.

The source family is the prior box with a nested raw Mu and an outer raw Mu. The inner body is a nullary tag17 row. The outer body is `union[var0,nested]`. Its nested request reuses the first full payload. This component adds one constructed theorem. It adds no production theorem, canonical build, or new source family.

The proof calls `build_row_resumptions` once on the actual completed closed build. It retains one path, all indexed rooted sites, final writers, precompletion writers, and the full universal row-resumption clause. The final-cell selector chooses an outer publication in that same path. Full candidate equality aligns its stored body with the actual tagged Mu.

The proof applies that selected outer publication's fixed callback row clause to the concrete tag17 row. Finite rooted source paths restrict the recovered writer body to the nested node or outer union. The same returned callback SourceRow and filter rule out the nested node because its identity-filtered raw node cannot equal a full Mu. The returned UnionDescent, terminal kind, and nonunion fact then force the SAME returned terminal to be the nested binder. The proof removes only that tuple's node alternative. It retains the complete binder alternative unchanged.

That binder tuple includes the actual current probes, request, full selected payload at the terminal return and outer afterBody, finish equality, stored RowAt, and physical/issued suffixes. It also includes an earlier index `i < j` and writer in the SAME path, its rooted source receipt, exact key/full payload equality, missing-before-publication fact, actual issued prefix and callbacks, and suffix to the enclosing outer afterBody. One fixed raw callback of THAT earlier event precedes both the concrete tag17 raw SourceRow and the universal stored-row clause. The concrete SourceRow is not an assumed desired origin or a separate writer search.

The proof does not identify the recovered writer, event, terminal heap, or earlier callback with a manually chosen setup event or a separate old consumer. It does not choose numeric event indices or prove event uniqueness. The strict index decrease applies to this original source build. It is not a global original-binding or native progress rank. No native prefix, runtime completion, outer termination, used recursive child, or Haskell refinement is claimed.

The actual source-call helper block and the finite source/union forcing helper block are byte-identical to the frozen union-descent fixture. The public theorem aliases a private checked witness with an identical expanded type.

Three owned Lean jobs ran. The first failed because `prefix` is a reserved parser token. Its source and log remain unchanged. The second strict attempt passed with a zero-byte raw log after the identifier was renamed. The sole full public group passed. It prints `#check @`, full `#print`, and `#print axioms` under all eight print/linter settings. Its 3,847,621-byte log has no omissions or printer failures and uses only `propext`, `Classical.choice`, and `Quot.sound`. Every job uses pinned Lean 4.34.1, a fresh usage receipt, memory max/high 4 GiB, zero swap, and a five-minute cap. No jobs remain live. Mutable peaks are excluded; the final three-row snapshot is pinned.

The standalone verifier checks local source snapshots by default. `--live --root ROOT` also checks current repository bytes. Raw commands retain their original temporary paths. Earlier frozen packages remain unchanged.
''')
print(json.dumps(dict(source=sha(source),printer=sha(printer),sources=len(sources))))
