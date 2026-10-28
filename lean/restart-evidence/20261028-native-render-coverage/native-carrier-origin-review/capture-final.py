from pathlib import Path
import hashlib,json,shutil,re
R=Path('/home/tritlo/Code/mcfta')
B=Path('/tmp/mcfta-render-coverage-20261028')
O=B/'native-carrier-origin-review'
assert not (O/'FROZEN.json').exists()
sha=lambda b:hashlib.sha256(b).hexdigest()
def write(p,b):
 p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b);return {'path':str(p),'bytes':len(b),'sha256':sha(b)}
def dump(p,x): return write(p,(json.dumps(x,indent=2)+'\n').encode())
idx=json.loads((O/'source-index.json').read_text()); records={x['source']:x for x in idx['sources']}
def source(rel,spans,scope):
 p=R/rel;b=p.read_bytes();lines=b.splitlines(keepends=True)
 rec=records.get(str(p),{'source':str(p),'cuts':[]})
 whole=write(O/'sources'/rel,b)
 if 'whole' in rec: assert rec['whole']==whole,(rel,'changed whole')
 rec['whole']=whole;rec['reviewed_scope']=scope
 known={(c['first_line'],c['last_line']) for c in rec['cuts']}
 for first,last in spans:
  assert 1<=first<=last<=len(lines),(rel,first,last,len(lines))
  if (first,last) in known:continue
  c=write(O/'cuts'/rel/(str(first)+'-'+str(last)+'.txt'),b''.join(lines[first-1:last]))
  c.update(first_line=first,last_line=last);rec['cuts'].append(c)
 records[str(p)]=rec
stats=json.loads((B/'source-stats.json').read_text())
for x in stats['modules']:
 rel='lean/MicroCFTA/'+x['module']+'.lean';data=(R/rel).read_bytes()
 assert len(data)==x['bytes'] and sha(data)==x['sha256']
 lines=data.decode().splitlines();spans=[]
 for i,line in enumerate(lines):
  if line.startswith('theorem '):
   end=next(j for j in range(i,len(lines)) if ':= by' in lines[j]);spans.append((i+1,end+1))
 source(rel,spans,'Whole final source read. Public declarations and complete proofs reviewed. Actual strict source snapshots bind the installed bytes.')
source('cfta/src/Data/CFTA/Enumeration.hs',[(1049,1075)],'Only actual native rendering definitions 1049-1075 and earlier bounded public-entry excerpts read. Whole file preserved as identity; no claim to have read its complete body. No Haskell execution.')
note='lean/notes-current-native-render-coverage.md'
lines=(R/note).read_text().splitlines()
source(note,[(9,31),(37,68),(99,123),(148,181)],'Whole final 11351-byte note read. All new local claims, open coverage/carrier gates, scoped counterexample, Haskell assessment, and recorded validation are reviewed.')
# Every issued current command is preserved, including all nine nonzero attempts.
checks=[]
for p in sorted(B.iterdir()):
 if not p.is_dir() or p.name=='prior-public-readback' or not (p/'report.json').exists(): continue
 report=json.loads((p/'report.json').read_text());raw=(p/'raw.log').read_bytes()
 assert len(raw)==report['bytes'] and sha(raw)==report['sha256'],p
 assert report['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'},p
 copied=[]
 for f in sorted(p.rglob('*')):
  if f.is_file() and f.suffix in {'.json','.log','.lean','.txt','.py'}:
   dest=O/'checks'/p.name/f.relative_to(p);copied.append(write(dest,f.read_bytes()))
 checks.append({'name':p.name,'exit_code':report['exit_code'],'bytes':report['bytes'],'sha256':report['sha256'],'report':str(O/'checks'/p.name/'report.json'),'files':copied})
assert len(checks)==28 and sum(x['exit_code']!=0 for x in checks)==9
# Old readback is provenance, not a current command.
for f in (B/'prior-public-readback').iterdir():
 if f.is_file() and f.suffix in {'.json','.log','.lean'}:write(O/'integration/prior-public-readback'/f.name,f.read_bytes())
metadata=['modules.json','source-stats.json','strict-checks.json','source-validation.json','preservation-validation.json','root-contract-comparisons.json','audit-import-insertion.json','public-validation.json','public-prefix-comparison.json','new-public-blocks.txt','new-public-declarations.json','public-declarations.json','public-definitions.json','prior-public-declarations.json','prior-public-definitions.json','source-head.txt','source-commits.json','published-base.txt','literal-original-initial-packet.txt','prior-strong-sources.json','document-validation.json','document-paths.json']
for name in metadata:write(O/'integration'/name,(B/name).read_bytes())
for f in (B/'helper-drafts').iterdir():
 if f.is_file():write(O/'integration/helper-drafts'/f.name,f.read_bytes())
prior=(B/'prior-public-readback/raw.log').read_bytes();new=(B/'new-public-blocks.txt').read_bytes();full=(B/'public-readback-2/raw.log').read_bytes();pub=json.loads((B/'public-validation.json').read_text())
assert full==prior+new and len(prior)==1055726 and len(full)==1081831 and len(new)==26105
assert sha(full)==pub['sha256'] and sha(new)==pub['new_sha256']
dump(O/'integration/independent-check-validation.json',{'status':'pass','current_commands':len(checks),'nonzero_commands':sum(x['exit_code']!=0 for x in checks),'inherited_receipt_excluded':True,'all_raw_lengths_hashes_match':True,'measured_limits_all':{'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'},'checks':checks,'public_exact_prior_prefix':True,'prior_bytes':len(prior),'final_bytes':len(full),'new_bytes':len(new),'final_sha256':sha(full),'new_sha256':sha(new)})
# Preserve original bytes and exact insertions. Read scope excludes old historical prose.
docs=[];common=[]
for x in json.loads((B/'document-validation.json').read_text()):
 cur=(R/x['path']).read_bytes();assert len(cur)==x['bytes'] and sha(cur)==x['sha256']
 if 'offset' not in x:continue
 old=(B/'prior-documents'/x['path']).read_bytes();off=x['offset'];ins=cur[off:off+x['inserted_bytes']]
 assert len(old)==x['old_bytes'] and sha(old)==x['old_sha256']
 assert cur==old[:off]+ins+old[off:] and cur[:off]+cur[off+len(ins):]==old
 previous=write(O/'documents/prior'/x['path'],old)
 inserted=write(O/'documents/insertions'/(x['path']+'.insert'),ins)
 first=cur[:off].count(b'\n')+1;last=first+ins.count(b'\n')-1
 assert b''.join(cur.splitlines(keepends=True)[first-1:last])==ins
 cut=write(O/'cuts'/x['path']/(str(first)+'-'+str(last)+'.txt'),ins);cut.update(first_line=first,last_line=last)
 records[str(R/x['path'])]={'source':str(R/x['path']),'bytes':len(cur),'sha256':sha(cur),'cuts':[cut],'reviewed_scope':'Only exact new insertion read. Whole previous document bytes preserved as data and reconstruction checked; historical body not reread.'}
 docs.append({'source':str(R/x['path']),'current_bytes':len(cur),'current_sha256':sha(cur),'offset':off,'old':previous,'insert':inserted,'exact_inverse':True})
 common.append(ins[:2506])
assert len(docs)==9 and len(set(common))==1
assert len((R/note).read_bytes())==11351
assert sha((R/note).read_bytes())=='f1afea84cb8bc295d9d90344c854aed972f58dc0b4d4fdcdd50878cb3dcc54c2'
dump(O/'documents/document-reconstruction.json',{'status':'pass','source_head':(B/'source-head.txt').read_text().strip(),'all_nine_exact_inverses':True,'common_prefix_bytes':2506,'common_prefix_sha256':sha(common[0]),'findings_insert_bytes':3402,'reviewed_scope':'Whole new note and all nine exact insertions read. Historical bodies only byte-verified.','documents':docs})
dump(O/'source-index.json',{'sources':list(records.values())})
status=json.loads((O/'draft-status.json').read_text());status['status']='COMPLETE; ready for final exact-set seal';status['final_public_readback']='PASS public-readback-2; first Lean pass ordering metadata failure retained';status['final_note_sha256']=sha((R/note).read_bytes());dump(O/'draft-status.json',status)
print(json.dumps({'sources':len(records),'cuts':sum(len(x['cuts']) for x in records.values()),'commands':len(checks),'nonzero':sum(x['exit_code']!=0 for x in checks),'documents':len(docs),'note_sha256':sha((R/note).read_bytes())}))
