from pathlib import Path
import hashlib,json
repo=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-selector-capture-20261027');out=area/'selector-review';sha=lambda b:hashlib.sha256(b).hexdigest()
def put(rel,b):
 p=out/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b.encode() if isinstance(b,str) else b)
specs=[('lean/MicroCFTA/SourceCurrentEnumerationOrder.lean',[(1,130)],'Whole formal closure/order module inspected; source canonical-class and sortOn correspondence remain explicit boundaries.'),('lean/MicroCFTA/SourceEqualityRequiredCache.lean',[(17,24)],'Current Ready fields only; remaining whole bytes are provenance.'),('lean/MicroCFTA/InternedGuardedLanguage.lean',[(23,52),(109,136),(150,169)],'Actual ordinary acceptance, forest, edge meaning, and constructor laws; rest provenance.'),('lean/MicroCFTA/InternedEdgeResidency.lean',[(16,44)],'Actual stored rows and parent-to-edge residency; rest provenance.'),('lean/MicroCFTA/SourcePruningEnumerationNativeOrdinary.lean',[(23,33),(74,108)],'Actual ordinary selector call and old subset-only admission; rest provenance.'),('lean/MicroCFTA/SourcePruningEnumerationNativeBranches.lean',[(21,43)],'Actual prefix stopping and unchanged captured cache with advanced Caller/query.'),('lean/MicroCFTA/SourcePruningEnumerationNativeContinuations.lean',[(41,71),(111,127)],'Actual hook-before-sibling and stopped-hook boundary; rest provenance.'),('cfta/src/Data/CFTA/Enumeration.hs',[(253,263),(656,725),(776,787),(1230,1287),(1423,1431)],'Actual edge closure, ordering, raw/default/custom selector entry points and ordinary call sites.'),('cfta/src/Data/CFTA/Interned.hs',[(171,188)],'Actual reachable map inserts nodeEdges rows; no Lean physical-map theorem claimed.')]
rows=[]
for path,cuts,scope in specs:
 src=repo/path;b=src.read_bytes();lines=b.splitlines(keepends=True);copy='sources/'+src.name;put(copy,b)
 row={'source':str(src),'whole':{'path':copy,'bytes':len(b),'sha256':sha(b)},'review_scope':scope,'cuts':[]}
 for a,z in cuts:
  assert 1<=a<=z<=len(lines),(path,a,z,len(lines))
  raw=b''.join(lines[a-1:z]);p=f'cuts/{src.name}.{a}-{z}.txt';put(p,raw);row['cuts'].append({'path':p,'bytes':len(raw),'sha256':sha(raw),'first_line':a,'last_line':z})
 rows.append(row)
put('source-index.json',json.dumps({'sources':rows},indent=2)+'\n')
strict=area/'strict-selector-1'
for p in strict.rglob('*'):
 if p.is_file():put(str(Path('evidence/strict-selector-1')/p.relative_to(strict)),p.read_bytes())
report=json.loads((strict/'report.json').read_text());draft=(out/'drafts/v1/SourcePruningEnumerationSelectorLanguage.lean').read_bytes();assert sha(draft)==report['source_sha256']
raw=(strict/'raw.log').read_bytes();assert len(raw)==279 and sha(raw)==report['sha256'] and report['exit_code']==1
put('draft-status.json',json.dumps({'bundle':'OPEN','v1':{'path':'drafts/v1/SourcePruningEnumerationSelectorLanguage.lean','bytes':len(draft),'sha256':sha(draft),'original_status':'UNTETSTED source-only draft; no compiler by agent','current_status':'FAILED Root strict-selector-1; exact source and 279-byte diagnostic retained'},'repair_review':'Root V2 will unfold InternedGuardedLanguage.meaning at accepted before obtain; proof-only reduction, no statement change. No competing edit here.','new_predicates':0,'new_runtime_definitions':0,'strict_run_by':'Root'},indent=2)+'\n')
print(json.dumps({'status':'captured','sources':len(rows),'cuts':sum(len(x['cuts']) for x in rows),'draft_v1_sha256':sha(draft),'bundle':'OPEN'}))
