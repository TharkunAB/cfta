from pathlib import Path
import hashlib,json,difflib
R=Path('/home/tritlo/Code/mcfta');B=Path('/tmp/mcfta-native-carriers-20261028');O=B/'native-incoming-review'
assert not (O/'FROZEN.json').exists()
sha=lambda b:hashlib.sha256(b).hexdigest()
def out(p,b):
 p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b);return {'path':str(p),'bytes':len(b),'sha256':sha(b)}
def dump(p,x):return out(p,(json.dumps(x,indent=2)+'\n').encode())
specs=[
 ('SourcePruningEnumerationIncomingNode',[(1,96)],'Actual finish/run definitions read. Completion producer is preserved as identity, but is not used by the all-bounds observer.'),
 ('SourcePruningEnumerationIncomingCacheAdapter',[(20,60),(62,113)],'Actual adapt/run/erase and singleton-core definitions read. Resource producer is not used.'),
 ('SourcePruningEnumerationIncomingProper',[(1,132),(157,234)],'Existing all-bounds incoming and cache proof pattern read. The old theorem statements are not edited.'),
 ('SourcePruningEnumerationCarrierFrame',[(1,29)],'Whole Root-provided source read. Frame.carriers and Frame.references derive actual class/reference transport.'),
 ('EnumerationCarriers',[(18,86),(206,222)],'Carrier definitions, class/read/write transport and requested-class construction read. No graph-specific enumeration theorem is invoked.'),
 ('EnumerationGraphReferences',[(34,75),(175,200)],'Fragment/reference predicates, actual transport and residual law read. Later generic enumeration proof is not used.'),
 ('EnumerationCompressionFrame',[(20,89)],'Frame fields, total transport and actual representative/read frame APIs read.'),
 ('EnumerationDependencies',[(149,174)],'EnumeratedOrigin and actual pending-write origin lemma read.'),
 ('UnionFind',[(124,145),(224,232),(536,545)],'Actual findRoot correctness, SameClass definition and sameClass_root used. Other union-find proofs not reviewed.'),
 ('SourcePruningEnumerationOwnFinalizeProper',[(1,103)],'Whole exact actual allocation, own-batch, finalization and residual proof shape read.'),
 ('SourcePruningEnumerationCachedChild',[(10,46)],'Actual cached allocation and ordinary child preparation definitions read. Later producer not used by these observers.'),
 ('SourcePruningEnumerationCachedOwn',[(12,45)],'Actual ordered own suspension and preparation definitions read. Later completeness proof not used by these observers.'),
 ('SourcePruningEnumerationFinalize',[(15,35)],'Actual final action and indexed run definitions read. No final cache/property premise is imported.'),
 ('SourcePruningEnumerationSelectedEdge',[(20,48),(68,83)],'Actual result, residual finish and selected run definitions read. Full selected completion proof not used.'),
 ('EnumerationRenderability',[(26,44)],'Existing completed-write reference proof read and reused. Later generic enumerateOut carrier proof not used.')]
records=[]
for name,spans,scope in specs:
 rel=Path('lean/MicroCFTA')/(name+'.lean');p=R/rel;b=p.read_bytes();lines=b.splitlines(keepends=True)
 rec={'source':str(p),'whole':out(O/'sources'/rel,b),'cuts':[],'reviewed_scope':scope}
 for first,last in spans:
  assert 1<=first<=last<=len(lines),(name,len(lines),first,last)
  c=out(O/'cuts'/rel/(str(first)+'-'+str(last)+'.txt'),b''.join(lines[first-1:last]));c.update(first_line=first,last_line=last);rec['cuts'].append(c)
 records.append(rec)
# The Root v2 is retained separately from the immutable owner v1.
name='SourcePruningEnumerationIncomingCarriers.lean';v1=O/'drafts/v1'/name;v2=B/'root-drafts/v2'/name
assert sha(v2.read_bytes())=='49c6e5f5facdd35ab10bfd99eb8543b3b598edcb9642cfb8e5cb9e14bb687672'
out(O/'root-revisions/v2'/name,v2.read_bytes())
diff=''.join(difflib.unified_diff(v1.read_text().splitlines(keepends=True),v2.read_text().splitlines(keepends=True),fromfile='owner-v1',tofile='root-v2'))
out(O/'incoming-root-repair.diff',diff.encode())
def statements(p):
 lines=p.read_text().splitlines(keepends=True);result=[]
 for i,line in enumerate(lines):
  if line.startswith('theorem '):
   j=i
   while ':= by' not in lines[j]:j+=1
   result.append(''.join(lines[i:j+1]).split(':= by',1)[0])
 return result
assert statements(v1)==statements(v2) and len(statements(v1))==4
dump(O/'incoming-declaration-comparison.json',{'public_statements':4,'owner_v1_vs_actual_root_v2_byte_identical':True,'only_repair':'Remove one unreachable repeat alternative at original line 148; no gate, conclusion, proof suppression or runtime definition change.','statement_bytes':[len(x.encode()) for x in statements(v1)],'statement_sha256':[sha(x.encode()) for x in statements(v1)]})
checks=[]
for p in sorted(B.iterdir()):
 if p.is_dir() and (p/'report.json').exists() and (p.name.startswith('incoming-carriers-') or p.name.startswith('own-finalize-carriers-') or p.name.startswith('carrier-frame-')):
  report=json.loads((p/'report.json').read_text());raw=(p/'raw.log').read_bytes();assert len(raw)==report['bytes'] and sha(raw)==report['sha256']
  for f in p.rglob('*'):
   if f.is_file() and f.suffix in {'.lean','.json','.log','.txt'}:out(O/'checks'/p.name/f.relative_to(p),f.read_bytes())
  checks.append({'name':p.name,'exit_code':report['exit_code'],'bytes':report['bytes'],'sha256':report['sha256']})
dump(O/'source-index.json',{'sources':records})
dump(O/'capture-attempt-note.json',{'status':'Resolved evidence-only bounds error','first_attempt':'Requested IncomingProper cut through line 245 but actual file has 234 lines. Assertion stopped before source-index creation.','repair':'Use exact 157-234 adapter cut and exact 1-29 CarrierFrame cut. No Lean source edit or compilation.'})
own=O/'own-finalize/drafts/v1/SourcePruningEnumerationOwnFinalizeCarriers.lean'
dump(O/'draft-status.json',{'status':'OPEN; awaiting Root own-finalize check and final integration/public/docs cues','incoming':{'owner_v1_sha256':sha(v1.read_bytes()),'actual_root_v2_sha256':sha(v2.read_bytes()),'actual_strict2':'PASS exit0/empty raw','earlier_strict1':'FAIL 254B unreachable tactic; retained','public_statements_unchanged':True},'own_finalize':{'path':str(own),'bytes':own.stat().st_size,'sha256':sha(own.read_bytes()),'status':'UNTESTED owner v1'},'checks_captured':checks,'source_identities':len(records),'literal_cuts':sum(len(x['cuts']) for x in records),'no_compiler_or_runtime_run_by_owner':True,'no_endpoint_carrier_admission':True,'synthetic_empty_scope':'Pure structural SOME-0 carrier, without native availability, acceptance, CacheValid or successful continuation claim.'})
print(json.dumps({'sources':len(records),'cuts':sum(len(x['cuts']) for x in records),'checks':checks}))
