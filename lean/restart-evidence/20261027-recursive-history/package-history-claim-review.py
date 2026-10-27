from pathlib import Path
import json,hashlib,re,datetime
repo=Path('/home/tritlo/Code/mcfta');root=Path('/tmp/mcfta-recursive-history-20261027');out=root/'claim-review'
sha=lambda b:hashlib.sha256(b).hexdigest()
write=lambda p,b:((out/p).parent.mkdir(parents=True,exist_ok=True),(out/p).write_bytes(b))
modules=json.loads((root/'modules.json').read_text());validation=json.loads((root/'source-validation.json').read_text())
spans={
'SourcePruningEnumerationPendingLanguage':[(15,23)],
'SourcePruningEnumerationRecursiveCallbackLanguage':[(34,60)],
'SourcePruningEnumerationSelectedPrefixCanonical':[(18,24),(57,73)],
'SourcePruningEnumerationRetentionBoundary':[(16,24),(31,47)],
'SourcePruningEnumerationPrefixLanguage':[(31,60),(114,138),(195,213)],
'SourcePruningEnumerationRecursivePrefixLanguage':[(25,33),(49,72)],
'SourceFlatPruningPrefixLanguage':[(28,56),(60,69),(132,172)]}
sources=[];cuts=[];evidence=[];documents=[]
def source(path,parts,copy=True,scope='whole final module and proof route read'):
 p=repo/path;raw=p.read_bytes();s={'path':str(p),'source':str(p),'bytes':len(raw),'sha256':sha(raw),'read_scope':scope}
 if copy:
  dest=Path('inputs')/path;write(dest,raw);s['snapshot']=str(dest)
 sources.append(s);lines=raw.splitlines(keepends=True)
 for start,end in parts:
  assert 1<=start<=end<=len(lines),(path,start,end,len(lines))
  b=b''.join(lines[start-1:end]);dest=Path('cuts')/(p.stem+f'--{start}-{end}'+p.suffix);write(dest,b)
  cuts.append({'path':str(p),'source':str(p),'snapshot':str(dest),'start':start,'end':end,'source_sha256':sha(raw),'bytes':len(b),'sha256':sha(b)})
 return s
for m in modules:source('lean/MicroCFTA/'+m+'.lean',spans[m])
source('lean/MicroCFTA/SourcePruningEnumerationRecursiveCallback.lean',[(29,45)],scope='original callback public contract and producer proof')
source('lean/MicroCFTA/SourcePruningEnumerationRecursivePrefix.lean',[(64,72)],scope='original recursive packet prefix contract and producer proof')
source('lean/MicroCFTA/SourceFlatPruningPrefixCompletion.lean',[(113,147)],scope='original flat prefix contract and single producer proof')
packet=source('lean/MicroCFTA/SourcePruningEnumerationRecursivePacket.lean',[(21,40)],scope='unchanged Packet fields; equality to prior snapshot')
assert (repo/'lean/MicroCFTA/SourcePruningEnumerationRecursivePacket.lean').read_bytes()==(root/'semantic-gates-review/inputs/lean/MicroCFTA/SourcePruningEnumerationRecursivePacket.lean').read_bytes()
source('lean/MicroCFTA/Audit.lean',[(1,7)],copy=False,scope='seven added imports and actual strict source hash; historical body not reread')
source('cfta/src/Data/CFTA/Enumeration.hs',[(1195,1207)],copy=False,scope='explicit public opaque-truncation contract only; earlier source review reused')
oldHashes={
'SourceCurrentColdFiniteWarmCalls':'e4665b0bb522ec88f1925fe6bc360b76e9e4bdfbe6192210ac708a3097a20cc5',
'SourcePruningEnumerationCapturedRendering':'18a81a7cdf0b208021f9ad5097e616270ad6001dbc75b08a7901352d5e174386',
'SourceFlatPruningCapturedResourceRendering':'73cba61e74141a8d2dc932eadf14372926b6318d0ceded73b774ec1c6fea57ef'}
for m,h in oldHashes.items():
 s=source('lean/MicroCFTA/'+m+'.lean',[],False,'unchanged whole source identity; prior source review reused; installed signature byte-comparison below');assert s['sha256']==h
for x in validation['strict_checks']:
 p=repo/'lean/MicroCFTA'/(x['module']+'.lean');b=p.read_bytes();assert sha(b)==x['sha256'];assert b==(root/'installed-sources/lean/MicroCFTA'/(x['module']+'.lean')).read_bytes()
 d=root/x['check'];q=json.loads((d/'report.json').read_text());raw=(d/'raw.log').read_bytes();assert q['exit_code']==0 and q['source_sha256']==sha(b) and q['bytes']==len(raw) and q['sha256']==sha(raw)
 assert '-DwarningAsError=true' in q['command'] and '-Dlinter.all=true' in q['command']
 assert q['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
 if x['module']!='Audit':
  assert raw==b'';assert not re.search(r'\bsorry\b|\baxiom\b|\bnative_decide\b|set_option\s+maxHeartbeats',b.decode())
 else:assert raw==b'Checked axiom dependencies of 79176 MicroCFTA theorems.\n'
def ev(relative,role):
 p=root/relative;b=p.read_bytes();dest=Path('evidence')/relative;write(dest,b);evidence.append({'path':str(p),'source':str(p),'snapshot':str(dest),'bytes':len(b),'sha256':sha(b),'role':role})
for x in validation['strict_checks']:
 for name in ['report.json','raw.log']:ev(x['check']+'/'+name,'final actual strict evidence; seven empty logs, Audit informational log')
for path in ['modules.json','strict-checks.json','source-validation.json','source-commits.json','public-validation.json','document-validation.json','published-base.txt','build-aggregate-final/report.json','build-aggregate-final/raw.log','public-readback-final/public.lean','public-readback-final/report.json','public-readback-final/raw.log','prior-public-readback/report.json','prior-public-readback/validation.json','prior-public-readback/raw.log']:
 ev(path,'retained actual check, source or provenance evidence')
for path in ['semantic-gates-review/FROZEN.json','semantic-gates-review/pins.json','semantic-gates-review/source-pins.json']:
 ev(path,'earlier immutable source-only proposal controls; not a passing proof claim')
for check in ['strict-retention-boundary-1','strict-prefix-language-1','strict-prefix-language-2','strict-recursive-prefix-language-1']:
 for name in ['report.json','raw.log']:ev(check+'/'+name,'retained earlier failed check; not current validation')
# Exact public signature/axiom preservation, with literal original line cuts.
public=(root/'public-readback-final/raw.log').read_bytes();prior=(root/'prior-public-readback/raw.log').read_bytes();pv=json.loads((root/'public-validation.json').read_text());assert len(public)==pv['bytes'] and sha(public)==pv['sha256']
comparison=[]
for name in pv['unchanged_prior_signatures']:
 key='MicroCFTA.'+name
 def block(raw):
  text=raw.decode();start=re.search('^'+re.escape(key)+r'(?=\s|$)',text,re.M).start();ax=text.index("'"+key+"' depends on axioms:",start);end=text.index(']',ax)+1
  return text[start:end].encode(),text[:start].count('\n')+1,text[:end].count('\n')+1
 new,ns,ne=block(public);old,os,oe=block(prior);assert new==old
 rec={'name':key,'bytes':len(new),'sha256':sha(new),'identical':True,'final_start':ns,'final_end':ne,'prior_start':os,'prior_end':oe};comparison.append(rec)
 for rel,raw,start,end,label in [('public-readback-final/raw.log',public,ns,ne,'final'),('prior-public-readback/raw.log',prior,os,oe,'prior')]:
  b=b''.join(raw.splitlines(keepends=True)[start-1:end]);dest=Path('cuts')/(name.split('.')[-1]+'--'+label+'.txt');write(dest,b)
  cuts.append({'path':str(root/rel),'source':str(root/rel),'snapshot':str(dest),'start':start,'end':end,'source_sha256':sha(raw),'bytes':len(b),'sha256':sha(b)})
write(Path('signature-comparison.json'),(json.dumps(comparison,indent=2)+'\n').encode())
# The common region is reviewed once; each literal region and removal is verified.
regions=[]
for x in json.loads((root/'document-validation.json').read_text()):
 path=x['path'];raw=(repo/path).read_bytes();assert len(raw)==x['bytes'] and sha(raw)==x['sha256']
 if 'offset'in x:
  start=x['offset'];end=start+x['inserted_bytes'];b=raw[start:end];old=(root/'prior-documents'/path).read_bytes();assert raw[:start]+raw[end:]==old;regions.append(b)
  dest=Path('documents/prefixes')/path;write(dest,b)
  documents.append({'path':str(repo/path),'source':str(repo/path),'snapshot':str(dest),'source_bytes':len(raw),'source_sha256':sha(raw),'byte_start':start,'byte_end_exclusive':end,'bytes':len(b),'sha256':sha(b),'prior_source':str(root/'prior-documents'/path),'prior_bytes':len(old),'prior_sha256':sha(old),'removal_exact':True,'read_scope':'only inserted region read; historical bytes compared, not reread or recopied'})
 else:
  dest=Path('documents')/path;write(dest,raw);documents.append({'path':str(repo/path),'source':str(repo/path),'snapshot':str(dest),'bytes':len(raw),'sha256':sha(raw),'read_scope':'whole final new note read'})
assert len(regions)==9 and all(x==regions[0] for x in regions) and len(regions[0])==1678
assert sum((repo/'lean/MicroCFTA'/(m+'.lean')).read_bytes().count(b'\n') for m in modules)==913
index={'version':1,'status':'FINAL CLEAR','observed_at':datetime.datetime.now().astimezone().isoformat(),'sources':sources,'cuts':cuts,'documents':documents,'evidence':evidence,'public_signature_comparison':'signature-comparison.json','unchanged_packet_sha256':packet['sha256'],'source_head':'a5973ba4a9ee69f8c62a1a5c853aca83e9c0eaed','read_scope':'All seven new sources; eleven new public signatures and three definitions; original wrapper contracts; note and common inserted region. Prior three signatures compared byte-for-byte. No build or historical whole-document reread.','limits':'Component prefix/callback meaning only. Whole recursive acceptance/coverage and lost-obligation history remain open.'}
write(Path('source-pins.json'),(json.dumps(index,indent=2)+'\n').encode())
for s in sources:
 assert sha(Path(s['source']).read_bytes())==s['sha256']
 if 'snapshot'in s:assert (out/s['snapshot']).read_bytes()==Path(s['source']).read_bytes()
for c in cuts:assert (out/c['snapshot']).read_bytes()==b''.join(Path(c['source']).read_bytes().splitlines(keepends=True)[c['start']-1:c['end']])
files=[p for p in sorted(out.rglob('*'))if p.is_file()and p not in {out/'pins.json',out/'FROZEN.json'}]
pins={'version':1,'pins':[{'path':str(p.relative_to(out)),'bytes':p.stat().st_size,'sha256':sha(p.read_bytes())}for p in files]};pinraw=(json.dumps(pins,indent=2)+'\n').encode();write(Path('pins.json'),pinraw)
freeze={'status':'FROZEN FINAL CLEAR','pins_count':len(files),'pins_bytes':len(pinraw),'pins_sha256':sha(pinraw),'source_count':len(sources),'source_whole_snapshots':sum('snapshot'in s for s in sources),'cut_count':len(cuts),'cut_lines':sum(c['end']-c['start']+1 for c in cuts),'document_count':len(documents),'evidence_count':len(evidence),'report_sha256':sha((out/'report.txt').read_bytes()),'source_pins_sha256':sha((out/'source-pins.json').read_bytes()),'new_checks_executed':False}
write(Path('FROZEN.json'),(json.dumps(freeze,indent=2)+'\n').encode());print(json.dumps(freeze,indent=2));print('FROZEN SHA256',sha((out/'FROZEN.json').read_bytes()))
