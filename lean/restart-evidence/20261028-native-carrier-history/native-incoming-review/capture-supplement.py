from pathlib import Path
import hashlib,json
R=Path('/home/tritlo/Code/mcfta');B=Path('/tmp/mcfta-native-carriers-20261028');O=B/'native-incoming-review'
assert not (O/'FROZEN.json').exists()
sha=lambda b:hashlib.sha256(b).hexdigest()
def put(p,b):p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b);return {'path':str(p),'bytes':len(b),'sha256':sha(b)}
def dump(p,x):return put(p,(json.dumps(x,indent=2)+'\n').encode())
idx=json.loads((O/'source-index.json').read_text());records={x['source']:x for x in idx['sources']}
def add(name,spans,scope):
 rel=Path('lean/MicroCFTA')/(name+'.lean');p=R/rel;b=p.read_bytes();ls=b.splitlines(keepends=True)
 rec=records.get(str(p),{'source':str(p),'cuts':[]});rec['whole']=put(O/'sources'/rel,b);rec['reviewed_scope']=scope
 existing={(x['first_line'],x['last_line']) for x in rec['cuts']}
 for first,last in spans:
  assert 1<=first<=last<=len(ls),(name,len(ls),first,last)
  if (first,last) in existing:continue
  c=put(O/'cuts'/rel/(str(first)+'-'+str(last)+'.txt'),b''.join(ls[first-1:last]));c.update(first_line=first,last_line=last);rec['cuts'].append(c)
 records[str(p)]=rec
owned=['SourcePruningEnumerationIncomingCarriers','SourcePruningEnumerationOwnFinalizeCarriers','SourcePruningEnumerationTraversalResourcesCarriers','SourcePruningEnumerationSelectedEdgeResourcesCarriers','SourcePruningEnumerationCapturedEdgeResourcesCarriers']
for name in owned:
 ls=(R/'lean/MicroCFTA'/(name+'.lean')).read_text().splitlines();spans=[]
 for i,line in enumerate(ls):
  if line.startswith('theorem '):
   j=i
   while ':= by' not in ls[j]:j+=1
   spans.append((i+1,j+1))
 add(name,spans,'Whole final installed source and all owner/Root differences read. Public statement and complete proof reviewed. Actual check snapshot is retained separately.')
specs=[
 ('SourcePruningEnumerationChildCarriers',[(139,221)],'Whole actual Root child carrier source read. Initial Safe is needed; no Safe endpoint conclusion is supplied by the carrier observer.'),
 ('SourcePruningEnumerationTraversalResources',[(35,87),(88,229),(233,291)],'Whole first original resource producer and final projection read. Successful head resource shape supplies middleSafe and exact actual post/full Memos.'),
 ('SourcePruningEnumerationTraversalProper',[(1,50)],'Whole proper trace and complete proof read. Its weaker predicate does not supply the Safe premise for the present child carrier leaf.'),
 ('SourcePruningEnumerationTraversalResourcesProper',[(1,100)],'Whole existing full-resource-packet-plus-proper-observer wrapper read.'),
 ('SourcePruningEnumerationTraversalEndpointProper',[(1,68)],'Whole complete/stopped endpoint proper proof read. Raw trace stores no per-child safety certificate.'),
 ('SourcePruningEnumerationTraversalStableResourceLanguage',[(136,158),(193,218)],'Actual common sufficient-bound head alignment, middleSafe and full Memos/tail resource transport read; no language premise is supplied to new carrier theorems.'),
 ('SourcePruningEnumerationSelectedEdgeResources',[(48,96),(97,191)],'Whole original first resource theorem read. Actual own prefix, traversal, residual and stopped routes are enriched without changing admission.'),
 ('SourcePruningEnumerationCapturedEdgeResources',[(33,86),(87,191)],'Whole original first resource theorem read. Actual selected and finalizer resource calls and stopped prefix are retained.')]
for spec in specs:add(*spec)
checks=[]
for p in sorted(B.iterdir()):
 if not p.is_dir() or not (p/'report.json').exists():continue
 report=json.loads((p/'report.json').read_text());cmd=' '.join(report['command'])
 relevant=any(name in cmd for name in owned) or any(p.name.startswith(prefix) for prefix in ['carrier-frame-','incoming-carriers-','own-finalize-carriers-','traversal-resources-carriers-','selected-resources-carriers-','captured-resources-carriers-'])
 if not relevant:continue
 raw=(p/'raw.log').read_bytes();assert len(raw)==report['bytes'] and sha(raw)==report['sha256']
 for f in p.rglob('*'):
  if f.is_file() and f.suffix in {'.lean','.json','.log','.txt'}:put(O/'checks'/p.name/f.relative_to(p),f.read_bytes())
 checks.append({'name':p.name,'exit_code':report['exit_code'],'bytes':report['bytes'],'sha256':report['sha256'],'source_sha256':report.get('source_sha256')})
for n in ['traversal-contract-comparison.json']:
 if (B/n).exists():put(O/'root-comparisons'/n,(B/n).read_bytes())
dump(O/'source-index.json',{'sources':list(records.values())})
status=json.loads((O/'draft-status.json').read_text());status['status']='OPEN; final integration/public/docs cues pending';status['checks_captured']=checks;status['source_identities']=len(records);status['literal_cuts']=sum(len(x['cuts']) for x in records.values());status['own_finalize']['status']='Root actual strict2 PASS empty';status['own_finalize']['actual_sha256']='5da8afbc7f0e2061114e0f47ad5340f450b42f293c7e1eaee307b375c9370944'
for folder,name in [('traversal_resources',owned[2]),('selected_resources',owned[3]),('captured_resources',owned[4])]:
 p=R/'lean/MicroCFTA'/(name+'.lean');status[folder]={'status':'Root actual strict1 PASS empty; owner v1 unchanged','actual_sha256':sha(p.read_bytes())}
dump(O/'draft-status.json',status)
dump(O/'capture-attempt-note.json',{'status':'Resolved evidence-only cut-bound assertions','attempts':[{'requested':'IncomingProper 172-245','actual_lines':234},{'requested':'TraversalProper 22-56','actual_lines':50},{'requested':'TraversalStableResourceLanguage 193-220','actual_lines':218}],'scope':'Assertions stopped before source-index commit. Already written source copies were exact data. No Lean source change or compiler job. Final cuts use actual bounded spans.'})
print(json.dumps({'sources':len(records),'cuts':status['literal_cuts'],'checks':checks},indent=2))
