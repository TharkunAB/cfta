from pathlib import Path
import json,hashlib
R=Path('/home/tritlo/Code/mcfta');B=Path('/tmp/mcfta-native-partial-output-20261028');O=B/'program-origin-review';L=R/'lean/MicroCFTA';sha=lambda b:hashlib.sha256(b).hexdigest()
assert not(O/'FROZEN.json').exists();records={s['source']:s for s in json.loads((O/'source-index.json').read_text())['sources']}
def put(p,b):
 p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b);return {'path':str(p),'bytes':len(b),'sha256':sha(b)}
def add(p,spans,scope,dest=None):
 b=p.read_bytes();ls=b.splitlines(keepends=True);rel=p.relative_to(R) if p.is_relative_to(R) else Path('stage')/p.relative_to(B)
 d={'source':str(p),'whole':put(dest or O/'sources'/rel,b),'cuts':[],'reviewed_scope':scope}
 for first,last in spans:
  assert 1<=first<=last<=len(ls),(p,first,last,len(ls))
  x=put(O/'cuts'/rel/(str(first)+'-'+str(last)+'.txt'),b''.join(ls[first-1:last]));x.update(first_line=first,last_line=last);d['cuts'].append(x)
 records[str(p)]=d
add(L/'SourcePruningEnumerationPartialOutput.lean',[(27,78),(80,109),(129,156),(158,214)],'WHOLE final214-line native partial source and both complete failure logs/deltas read. Private boundary adapter supplies only literal native lookup recursive tag; no graph-language/intersection semantics asserted. Actual full stable endpoint precedes semantic models.')
add(L/'SourcePruningEnumerationHistoryPartialOutput.lean',[(39,80)],'WHOLE final82-line history partial source read. Actual own output Packet/order/carriers derive root allocation; callback_frame returns SAME full Packet after compression before models. No Discharged/future output-model admission.')
add(L/'SourcePruningEnumerationInitialPartialOutput.lean',[(35,62),(119,151)],'WHOLE final151-line startup partial source read. Entire old6435-byte declaration recovered exactly. Old startup producer once. Actual strict1 import-only failure and strict2 PASS retained; final direct carrier import matches actual producer.')
add(L/'SourcePruningEnumerationInitialRenderCarriers.lean',[(34,117)],'WHOLE old startup-render-carrier source read. Entire original declaration including all witnesses/old fields recovered from new appended partial observer.')
add(L/'EnumerationState.lean',[(334,357)],'Only existing partial-symbol and expandPartial definitions read for actual tag-only dependency; remaining runtime branches unreviewed here.')
add(L/'EnumerationUntil.lean',[(134,140)],'Literal rootFragment definition and nearby public partial-run sequence read; remaining driver proof bodies not reread.')
add(L/'EnumerationPartialRoot.lean',[(27,39),(60,67)],'WHOLE existing generic root partial frame/agreement/transport source read. Native tag adapter does not assert generic graph-language correspondence.')
add(L/'SourcePruningEnumerationRecursivePacket.lean',[(20,35),(50,62)],'WHOLE original recursive Packet/callback_frame source read. Same full caller/Memos/context/index/bounded-metadata packet retained after reads.')
a=(L/'SourcePruningEnumerationInitialRenderCarriers.lean').read_text();a=a[a.index('theorem run_initial_finite_render_sound_carriers'):].split(':= by',1)[0].rstrip()
n=(L/'SourcePruningEnumerationInitialPartialOutput.lean').read_text();n=n[n.index('theorem run_initial_finite_render_sound_partial'):].split(':= by',1)[0].rstrip()
p=n.rsplit(') ∧\n      ∀ output ∈ SourcePruningEnumerationHookInvocation.hookOutputs outcome,',1)[0].replace('theorem run_initial_finite_render_sound_partial','theorem run_initial_finite_render_sound_carriers',1).replace('      ((((∀ extra,','      (((∀ extra,',1)
assert a==p and len(a.encode())==6435
put(O/'contracts/entire-original-initial-carrier-declaration.txt',a.encode());put(O/'contracts/recovered-original-initial-carrier-declaration.txt',p.encode())
put(O/'contracts/startup-partial-contract-comparison.json',(json.dumps({'status':'pass','scope':'ENTIRE original declaration including theorem name, every input/handle/native lookup/literal startup/bound/outcome/old field. Trailing pre-proof whitespace trimmed; only theorem rename, one outer grouping and appended partial observer removed.','bytes':len(a.encode()),'sha256':sha(a.encode()),'byte_identical':True,'old_producer_calls':1,'new_admission':False},indent=2)+'\n').encode())
for name in ['native-partial-output-strict-1','native-partial-output-strict-2','native-partial-output-strict-3','history-partial-output-strict-1','initial-partial-output-strict-1','initial-partial-output-strict-2','partial-dependencies-build-1','history-partial-build-1']:
 d=B/name
 if not(d/'report.json').exists():continue
 r=json.loads((d/'report.json').read_text());raw=(d/'raw.log').read_bytes();assert len(raw)==r['bytes'] and sha(raw)==r['sha256']
 if 'source_sha256' in r:assert sha(Path(r['command'][-1]).read_bytes())==r['source_sha256']
 for f in sorted(d.rglob('*')):
  if f.is_file() and f.suffix in {'.json','.lean','.log','.txt'}:add(f,[],'Actual Root strict/build snapshot/full raw/report retained; hash/exit/source verified. All complete strict failure logs for these native/startup repairs read.',O/'checks'/name/f.relative_to(d))
for d in sorted((B/'root-drafts').iterdir()):
 if d.name.startswith(('v3-','v4-','v5-','v6-')):
  for f in sorted(d.rglob('*')):
   if f.is_file():add(f,[],'Whole Root source repair/exact delta retained and read within this integration review.',O/'lineage'/d.name/f.relative_to(d))
(O/'source-index.json').write_text(json.dumps({'sources':list(records.values())},indent=2)+'\n')
print(json.dumps({'sources':len(records),'cuts':sum(len(s['cuts']) for s in records.values()),'whole_old_startup_bytes':len(a.encode()),'whole_old_startup_sha256':sha(a.encode())},indent=2))
