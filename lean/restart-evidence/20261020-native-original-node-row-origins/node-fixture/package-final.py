from pathlib import Path
import hashlib,json,shutil
HERE=Path(__file__).resolve().parent
ROOT=Path('/home/tritlo/Code/mcfta')
PREFIX='node-row-origins-kernels'
NAME='MicroCFTA.OriginalNodeRowOriginsFixture.actual_strict_node_row_origin'
ATTEMPTS={PREFIX+'-direct-1':0,PREFIX+'-public-1':0}
def sha(data):return hashlib.sha256(data).hexdigest()
def write(name,value):(HERE/name).write_text(json.dumps(value,indent=2)+'\n')
source=(HERE/(PREFIX+'.lean')).read_bytes();printer=(HERE/(PREFIX+'-public.lean')).read_bytes()
assert sha(source)=='9fcedfe8f4af9c2ed8641d933810e4b02878abedd0195bc8f597b1dc1e68e89c'
assert sha(printer)=='898fa1551a67bade1bb2eec2ce3d0c373bd652633ec7964d1fb5fb44634e805b'
assert not (HERE/(PREFIX+'-direct-1.log')).read_bytes()
shutil.copyfile(HERE/(PREFIX+'-peaks.txt'),HERE/(PREFIX+'-peaks-final.txt'))
(HERE/'inputs').mkdir(exist_ok=True)
shutil.copyfile('/tmp/mcfta-native-original-indexed-resumption-fixture/indexed-resumption-kernels.lean',HERE/'inputs/prior-indexed-resumption-kernels.lean')
previous=json.loads(Path('/tmp/mcfta-native-original-indexed-resumption-fixture/indexed-resumption-kernels-source-pins.json').read_text())['sources']
paths=['lean/MicroCFTA/SourceCurrentNativeOriginalNodeRowOrigins.lean']+[x['path'] for x in previous]
sources=[]
for rel in paths:
 data=(ROOT/rel).read_bytes();snap='inputs/'+Path(rel).name
 (HERE/snap).write_bytes(data)
 sources.append(dict(path=rel,snapshot=snap,bytes=len(data),sha256=sha(data)))
assert sources[0]['sha256']=='77ebcd45a4f36f0118f175194ccf102bf9af2fb85173e80744a2e48dbeb6371d'
write(PREFIX+'-source-pins.json',dict(schema='portable-source-pins-v1',sources=sources))
write(PREFIX+'-selection.json',dict(schema='constructed-fixture-selection-v1',finalized=True,source=PREFIX+'.lean',source_sha256=sha(source),printer_sha256=sha(printer),strict=PREFIX+'-direct-1',groups=[dict(name=PREFIX+'-public-1',pairs=1,kind='constructed',full_proof=True)],public_heads=[NAME],attempts=list(ATTEMPTS),expected_exit_codes=ATTEMPTS,lean_jobs=2,failed_attempts=0,production_pairs=0,constructed_pairs=1,canonical=None,canonical_jobs=0,distinct_new_source_examples=0,source_data_helpers_byte_identical=True,source_forcing_helpers_byte_identical=True))
(HERE/(PREFIX+'-review.md')).write_text('''# Strict original node-row fixture

Reviewed at 2026-10-20 23:23 CEST.

The source family is the prior box with a nested raw Mu and an outer raw Mu. The nested body has a nullary tag17 row. The outer body is `union[var0,nested]`. The nested request reuses the first full payload. This component adds one constructed theorem. It adds no production theorem, canonical build, or new source family.

The proof calls `build_node_row_origins` once on the actual completed closed source build. It retains the returned publication path, indexed rooted sites, final full-cell writer selector, and universal actual node-row origins. It uses that final selector to choose an outer writer in the same path. Full candidate equality aligns its stored body with the actual tagged Mu. The concrete tag17 stored row is therefore nonvacuous.

The public `publication_body_origin` helper derives a raw callback SourceRow for THAT SAME chosen outer event. Finite rooted source paths and that callback's actual filter prove its expression is the outer union. This does not select another publication. The universal node-row clause then gives one actual node producer in the same path at index k <= j. If k = j, the two lookups in that SAME list derive producer = outer. Its returned UnionDescent would then go from the outer union through only union members to a node. The only members are a variable and the nested binder, so that route is impossible. Thus the SAME returned node producer has k < j.

The complete public type retains that producer lookup, generic syntax bound, union route, Context, rooted source entry, SourceRow, actual node build, actual buildEdges and makeNode, canonical row lookup, and RowCall whose output is the SAME full tag17 EdgeValue. Source and output indices remain separate fields. The row is nullary. No child-existence premise is used. The physical and issued suffix ends at the SAME outer.afterBody. The source row is a stored row. It is not a later changed unfold row.

The only event equality used is DERIVED in the hypothetical equal-index branch from the same path lookup. The proof does not equate a recovered event with the manual setup event, choose numeric indices, or prove event uniqueness. The strict index is chronology within one completed original source build. It is not a global native runtime rank, original-binding rank, termination theorem, native query result, or Haskell refinement claim. No new source family or used recursive child is asserted.

The actual source-call and finite forcing helper blocks are byte-identical to the frozen indexed-resumption fixture. The new pure route contradiction and strictness argument follow them. The public theorem aliases a private checked witness with an identical expanded type.

Two owned Lean jobs ran. Both passed on the first attempt. The selected strict raw log has zero bytes. The sole full public group prints `#check @`, full `#print`, and `#print axioms` under all eight print/linter settings. Its 1,468,808-byte log has no omissions or printer failures and uses only `propext`, `Classical.choice`, and `Quot.sound`. Each job uses pinned Lean 4.34.1, a fresh usage receipt, memory max/high 4 GiB, zero swap, and a five-minute cap. No jobs remain live. Mutable peaks are excluded; the final two-row snapshot is pinned.

The standalone verifier checks local source snapshots by default. `--live --root ROOT` also checks repository source bytes. Raw commands retain their original temporary paths. Earlier frozen packages remain unchanged.
''')
print(json.dumps(dict(source=sha(source),printer=sha(printer),sources=len(sources))))
