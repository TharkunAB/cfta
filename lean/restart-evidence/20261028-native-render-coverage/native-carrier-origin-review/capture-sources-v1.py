from pathlib import Path
import hashlib,json,shutil,difflib
repo=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-render-coverage-20261028');out=area/'native-carrier-origin-review'
def sha(b):return hashlib.sha256(b).hexdigest()
items=[
('EnumerationCarriers.lean',[(19,29),(38,85),(241,255)],'Graph-independent definitions, class/write/allocation carrier algebra and residual/suspension laws read. Generic graph-specific proof portions read for comparison; no Graph correspondence inferred.'),
('EnumerationGraphReferences.lean',[(37,69),(188,211),(219,244)],'Reference definitions, transport, residual and traversal helpers read; whole mutual graph proof not fully reread.'),
('EnumerationRenderability.lean',[(20,44)],'Read class-preserving and write-reference helpers and graph enumerateOut proof through line105. Later graph run proof unreviewed.'),
('EnumerationRendering.lean',[(39,70),(128,145)],'Whole finite graph rendering proof read. It provides proof shape only; no fabricated CompleteGraph instantiated.'),
('SourcePruningEnumerationRendering.lean',[(22,66),(143,170)],'Native renderer operations and discharged definition read; existing assignment proof input inspected. Complete private soundness proof not reread.'),
('SourcePruningEnumerationShallowChild.lean',[(17,35),(39,67)],'Whole actual native preparation and complete readback proof read.'),
('SourcePruningEnumerationCachedPrepare.lean',[(10,33),(36,104),(311,366)],'Actual runtime and erasure proof read; allocation/boundary/full producer statements and proof used for route comparison. Whole366line proof not fully reread.'),
('SourcePruningEnumerationCachedPrepareProper.lean',[(21,89),(102,122)],'Whole actual shallow and row Proper proof read as proof convention/source inversion reference; no theorem edited.'),
('SourcePruningEnumerationPreparedCarriers.lean',[(21,44),(64,80),(109,125)],'Whole final126line root-corrected source read, compared to original draft; strict1/2 failures and strict3 success read.'),
('SourcePruningEnumerationInitialCarriers.lean',[(27,57)],'Whole new original startup-wrapper source read; original packet call once, actual root carrier/reference proof checked.'),
('SourcePruningEnumerationRecursivePacket.lean',[(20,34),(65,79)],'Whole Packet definition and packet transport source read. It does not assert graph-bearing holes.'),
('SourcePruningEnumerationFiniteHistoryContract.lean',[(41,109)],'ResourceHistory constructor fields read; later completion/zero proof not reread. Actual selected prefix, ordinary receipt/callback and tail endpoints compared.'),
('SourcePruningEnumerationResourceHistoryProper.lean',[(40,84)],'Whole history Proper induction read. It carries only ProperState and does not supply ReferencesCarry.'),
('SourcePruningEnumerationFinalize.lean',[(16,35),(65,88)],'Whole literal finalizer and complete output proof read. Its slot write is completed fragment; carrier proof must supply actual fragment holes.'),
('SourcePruningEnumerationSelectedEdge.lean',[(29,42),(67,84)],'Actual runtime plus result and residual operations read; producer declaration read through first result-shape fields. Full original proof not reread.'),
('SourcePruningEnumerationCapturedEdge.lean',[(23,33),(73,93)],'Actual finalization wrapper and original producer declaration through its result shape read; full old proof not reread.'),
('SourcePruningEnumerationRecursion.lean',[(17,32),(56,70)],'Actual recursion guard and complete packet read through line135. Parked clears only bucket while retaining SOME native handle.'),
('SourcePruningEnumerationAction.lean',[(17,39),(77,101)],'Actual narrowing action and complete pending proof prefix read through line110. Successful changed-handle action writes SOME handle.'),
('SourcePruningEnumerationIncomingNode.lean',[(28,36),(167,185)],'Incoming runtime/finish and completion fields inspected for precise next terminal route; full proof not reread.'),
('EnumerationCorrectness.lean',[(142,146),(620,651)],'State satisfaction and storage-bound definitions, nearby exact-operation lemmas read for counterexample and draft proofs; rest unreviewed.'),
('EnumerationSchedule.lean',[(273,279),(1111,1113)],'LiveRoots and Safe definitions plus primitive exactness/local snippets inspected; whole large source not reread.')]
records=[]
for name,spans,scope in items:
 rel=Path('lean/MicroCFTA')/name;src=repo/rel;b=src.read_bytes();dest=out/'sources'/rel;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(b);cuts=[]
 for first,last in spans:
  assert last<=len(b.splitlines()),(name,last)
  data=b''.join(b.splitlines(True)[first-1:last]);cut=out/'cuts'/rel/f'{first}-{last}.txt';cut.parent.mkdir(parents=True,exist_ok=True);cut.write_bytes(data)
  cuts.append({'path':str(cut),'bytes':len(data),'sha256':sha(data),'first_line':first,'last_line':last})
 records.append({'source':str(src),'whole':{'path':str(dest),'bytes':len(b),'sha256':sha(b)},'cuts':cuts,'reviewed_scope':scope})
(out/'source-index.json').write_text(json.dumps({'sources':records,'scope':'Actual native carrier-origin observer, startup review and scoped pure-state non-renderability investigation. No compiler/runtime/Git/network/board by reviewer.'},indent=2)+'\n')
for name in ['prepared-carriers-strict-1','prepared-carriers-strict-2','prepared-carriers-strict-3','initial-carriers-strict-1','initial-carriers-strict-2']:
 for p in (area/name).rglob('*'):
  if p.is_file() and p.suffix not in ['.olean','.ilean','.c','.o']:
   q=out/'checks'/name/p.relative_to(area/name);q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
original=(out/'drafts/v1/SourcePruningEnumerationPreparedCarriers.lean').read_text();final=(repo/'lean/MicroCFTA/SourcePruningEnumerationPreparedCarriers.lean').read_text()
(out/'prepared-root-repair.diff').write_text(''.join(difflib.unified_diff(original.splitlines(True),final.splitlines(True),fromfile='own-untested-v1',tofile='actual-strict3-final')))
(out/'draft-status.json').write_text(json.dumps({'status':'OPEN','prepared_carriers':{'original':'drafts/v1/SourcePruningEnumerationPreparedCarriers.lean','final_actual_sha256':sha(final.encode()),'strict3':'PASS exit0/emptyraw','public_theorem_declarations_unchanged':True},'free_hole':{'current_candidate':'drafts/v5/SourcePruningEnumerationFreeHole.lean','status':'UNTESTED pending Root; earlier variants retained UNTESTED','no_claims':['full Packet counterexample','actual startup reachability','Haskell runtime defect']},'global_native_history_carriers':'OPEN'},indent=2)+'\n')
print(len(records),'whole source identities',sum(len(r['cuts']) for r in records),'literal cuts')
