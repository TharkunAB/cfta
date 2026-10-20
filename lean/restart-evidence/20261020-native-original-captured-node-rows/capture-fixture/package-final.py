from pathlib import Path
from datetime import datetime
from zoneinfo import ZoneInfo
import hashlib,json,shutil
HERE=Path(__file__).resolve().parent
ROOT=Path('/home/tritlo/Code/mcfta')
PREFIX='captured-node-rows-kernels'
NAME='MicroCFTA.OriginalCapturedNodeRowsFixture.actual_initial_captured_node_row'
ATTEMPTS={PREFIX+'-direct-1':0,PREFIX+'-public-1':0}
def sha(data):return hashlib.sha256(data).hexdigest()
def write(name,value):(HERE/name).write_text(json.dumps(value,indent=2)+'\n')
source=(HERE/(PREFIX+'.lean')).read_bytes();printer=(HERE/(PREFIX+'-public.lean')).read_bytes()
assert sha(source)=='721138d4a0ab8a882527ed764e707695173bcf6a1699d470a450e070da89b90d'
assert sha(printer)=='2ab4a9747e277c5ff21d2a1971e4c625fb587ce1530390f655405ba4e9697eb4'
assert not (HERE/(PREFIX+'-direct-1.log')).read_bytes()
shutil.copyfile(HERE/(PREFIX+'-peaks.txt'),HERE/(PREFIX+'-peaks-final.txt'))
(HERE/'inputs').mkdir(exist_ok=True)
shutil.copyfile('/tmp/mcfta-native-original-terminal-fixture/terminal-kernels.lean',HERE/'inputs/prior-terminal-kernels.lean')
prior=json.loads(Path('/tmp/mcfta-native-original-terminal-fixture/terminal-kernels-source-pins.json').read_text())['sources']
node=json.loads(Path('/tmp/mcfta-native-original-node-row-origins-fixture/node-row-origins-kernels-source-pins.json').read_text())['sources']
paths=list(dict.fromkeys(['lean/MicroCFTA/SourceCurrentNativeOriginalCapturedNodeRows.lean']+[x['path'] for x in prior+node]))
sources=[]
for rel in paths:
 data=(ROOT/rel).read_bytes();snap='inputs/'+Path(rel).name
 (HERE/snap).write_bytes(data)
 sources.append(dict(path=rel,snapshot=snap,bytes=len(data),sha256=sha(data)))
assert sources[0]['sha256']=='73a58a83d3c46233c245f10be1f301649626d7bb50149a19d02a821c399c0d51'
write(PREFIX+'-source-pins.json',dict(schema='portable-source-pins-v1',sources=sources))
write(PREFIX+'-selection.json',dict(schema='constructed-fixture-selection-v1',finalized=True,source=PREFIX+'.lean',source_sha256=sha(source),printer_sha256=sha(printer),strict=PREFIX+'-direct-1',groups=[dict(name=PREFIX+'-public-1',pairs=1,kind='constructed',full_proof=True)],public_heads=[NAME],attempts=list(ATTEMPTS),expected_exit_codes=ATTEMPTS,lean_jobs=2,failed_attempts=0,production_pairs=0,constructed_pairs=1,canonical=None,canonical_jobs=0,distinct_new_source_examples=0,source_data_helpers_byte_identical=True,initial_branch_forced=True,nonidentity_unfold_calls=True,leaves_occurrence=1,encode_slot_claim=False))
review='''# Actual initial capture and original node-row fixture

Reviewed at TIMESTAMP.

The source family is the prior native initial-capture family from fixture65157a03. Two distinct closed used outer Mu values share the same closed used inner Mu. Each inner body has a recursive unary row and a nullary shared tag. This family differs from the source-only warm box family. It adds no new source family here. This component adds one constructed theorem and no production theorem or canonical build.

The exact closed build returns the heap in the initial native machine. The actual Top field allocation, source annotations, physical cache validity, and source facts derive initial Good. Empty native memo state derives native memo History. The admission certificate derives the checked requestNode Trace and site-body availability from the computed bounded execution to the outer optional. The leaf pool contains the initial inner full Mu at occurrence one. This is a leaves occurrence. No encode.slot equality is asserted.

The proof calls capture_node_rows once. Its generated alternative requires the same key to be absent at an earlier optional site. The actual initial full cell and that branch's actual forward prefix growth contradict this absence. Thus the returned initial arm is nonvacuous. The proof retains its one source-derived path, indexed rooted sites, final writer selector, one chosen indexed outer writer and full payload alignments, all stored-row node origins, current semantic/availability/publication-history support, and all actual-unfold clauses. It does not call an old capture or an independent writer producer.

The same captured full Mu actually unfolds at the SAME current heap. The selected literal rec/Top row has one full-Mu child. The original stored rec row has one own-reference child. The computed rows differ. The returned stored anchor is identified with that exact stored rec row by its unique symbol. The identity alternative is impossible, so the returned actual ordered substitution Calls remain in the public result. The original node RowCall equals that SAME stored row, including its stored reference child. It does not equal the changed unfolded row. Symbol, guard, arity, and actual Calls connect the two rows.

The concrete node origin retains the SAME path and selected writer index as the generic initial arm. It includes producer k <= j and lookup, generic SyntaxBound/UnionDescent, rich Context, original Reached, SourceRow, actual node/buildEdges/makeNode equations, separate source and output indices, canonical stored-row lookup, full RowCall output equality, and physical/issued suffix to the chosen writer's afterBody. No event identity with an earlier independently selected receipt is assumed.

The source, data, admission, and unfold helper block is byte-identical to the frozen predecessor65157a03. Only imports, header, namespace, and the final consumer proof change. The public theorem aliases a private checked witness with an identical expanded type.

Two owned Lean jobs ran. Both passed on the first attempt. The selected strict raw log has zero bytes. The full public group prints check-at, full print, and axioms under all eight print/linter settings. Its 2,105,277-byte log has no omissions or printer failures. Its axioms are only propext, Classical.choice, and Quot.sound. Each job uses pinned Lean4.34.1, a fresh usage receipt, memory max/high4GiB, zero swap, and a five-minute cap. No jobs remain live. Mutable peaks are excluded; the final two-row snapshot is pinned.

The actual native execution stops before the outer optional. The fixture does not show a new native generated capture or execute the outer optional. The successful unfold is an actual checked source operation at the current heap. It does not prove native runtime termination, productivity, arbitrary projection continuation, global renewal, or Haskell refinement. The unchanged generated branch is part of the production theorem, not the branch exercised by this example.

The standalone verifier checks local source snapshots by default. Live mode with a root argument also checks repository bytes. Raw commands retain their original temporary paths. Earlier frozen source and evidence packages remain unchanged.
'''
review=review.replace('TIMESTAMP',datetime.now(ZoneInfo('Europe/Stockholm')).strftime('%Y-%m-%d %H:%M %Z'))
(HERE/(PREFIX+'-review.md')).write_text(review)
print(json.dumps(dict(source=sha(source),printer=sha(printer),sources=len(sources))))
