from pathlib import Path
import datetime,hashlib,json,re
A=Path('/tmp/mcfta-worker-arity-20261027');P=A/'public-readback-final-1'
plan=json.loads((A/'public-metadata-plan.json').read_text())
raw=(P/'raw.log').read_bytes();lines=raw.splitlines(keepends=True)
H=lambda b:hashlib.sha256(b).hexdigest()
now=datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M:%S %Z')
report=json.loads((P/'report.json').read_text())
assert report['exit_code']==0 and len(raw)==report['bytes'] and H(raw)==report['sha256']
public=json.loads((A/'public-validation.json').read_text());assert public['status']=='pass'
starts=[i for i,line in enumerate(lines) if re.match(rb'^(?:MicroCFTA\.|structure MicroCFTA\.|def MicroCFTA\.)',line)]
blocks={}
for q,i in enumerate(starts):
 line=lines[i].decode();m=re.match(r'^(?:(?:structure|def) )?(MicroCFTA\.[^\s{(:]+)',line);assert m,line
 end=starts[q+1] if q+1<len(starts) else len(lines)
 blocks[m.group(1)]=(i,end,b''.join(lines[i:end]))
assert len(blocks)==93,len(blocks)
for bundle,own in [('probe-exposure',['SourcePruningEnumerationProbeExposureArity']),('target-leaf',['SourcePruningEnumerationSelectionArity','SourcePruningEnumerationMergeArity','SourcePruningEnumerationSharedTargetArity'])]:
 R=A/bundle;assert not(R/'FROZEN').exists()
 index=json.loads((R/'source-index.json').read_text())
 def capture(source,dest,scope,read='WHOLE',cuts=None):
  data=source.read_bytes();dest.parent.mkdir(parents=True,exist_ok=True)
  if dest.exists():assert dest.read_bytes()==data,(source,dest)
  else:dest.write_bytes(data)
  rec={'source':str(source),'snapshot':str(dest),'bytes':len(data),'sha256':H(data),'scope':scope,'reviewed_scope':read,'cuts':cuts or []}
  existing=[x for x in index['sources'] if x['snapshot']==str(dest)]
  if not existing:index['sources'].append(rec)
  else:assert existing[0]==rec
  return rec
 names=[d['name'] for m in plan['modules'] if m['module'] in own for d in m['theorems']]
 if bundle=='target-leaf':names+=plan['new_data_declarations']+plan['separate_public_predicate_definitions']
 cuts=[];joined=[]
 for name in names:
  first,last,data=blocks[name]
  if name not in plan['new_data_declarations']+plan['separate_public_predicate_definitions']:
   assert ("'"+name+"' depends on axioms:").encode() in data
  dest=R/'final-public/blocks'/(name+'.txt');dest.parent.mkdir(parents=True,exist_ok=True)
  if dest.exists():assert dest.read_bytes()==data
  else:dest.write_bytes(data)
  cuts.append({'first_line':first+1,'last_line':last,'snapshot':str(dest),'bytes':len(data),'sha256':H(data),'scope':'literal full public signature and axiom block, or full printed definition','purpose':name})
  joined.append(data)
 aggregate=R/'final-public/own-blocks.txt';aggregate.write_bytes(b''.join(joined))
 capture(P/'raw.log',R/'final-public/raw.log','whole actual final public output identity','ONLY own complete blocks listed in cuts; other final blocks by retained root validator',cuts)
 for source in [P/'report.json',P/'public.lean',A/'public-validation.json',A/'source-validation.json',A/'modules.json',A/'strict-checks.json',A/'public-declarations.json',A/'public-definitions.json']:
  capture(source,R/'final-evidence'/source.name,'whole final source/public/check metadata','WHOLE')
 for check in ['build-audit-1','strict-audit-1']:
  rp=json.loads((A/check/'report.json').read_text());rr=(A/check/'raw.log').read_bytes()
  assert rp['exit_code']==0 and len(rr)==rp['bytes'] and H(rr)==rp['sha256']
  for fn in ['report.json','raw.log']:capture(A/check/fn,R/'final-evidence'/check/fn,'whole actual successful final integration evidence')
 # Check all frozen-independent original strongest public blocks.
 old=[]
 for retained in plan['retained_previous_literal_blocks']:
  current=blocks[retained['name']][2];prior=Path(retained['snapshot']).read_bytes()
  # The final old block ends before definitions; the prior final block reaches EOF.
  assert current==prior,(retained['name'],'old public block changed')
  old.append({'name':retained['name'],'bytes':len(current),'sha256':H(current),'literal_equal':True})
 status={'measured_time':now,'status':'CHECKED FINAL EVIDENCE; own public semantic reading pending final report',
  'own_modules':own,'own_theorem_blocks':len(names)-(2 if bundle=='target-leaf' else 0),'own_definition_blocks':2 if bundle=='target-leaf' else 0,
  'all_own_blocks_complete':True,'public_bytes':len(raw),'public_sha256':H(raw),'old_twelve_literal_equal':old,
  'aggregate_build':'PASS4195 jobs / 79883 theorem dependencies','strict_audit':'PASS,56B expected printed output',
  'source_validation':'PASS17 module/Audit source checks','public_validation':'PASS91 signatures,79 new,12 unchanged,2 full definitions,std3axioms,no elision',
  'final_source_identities':[m['source'] for m in plan['modules'] if m['module'] in own]}
 (R/'final-evidence/status.json').write_text(json.dumps(status,indent=2)+'\n')
 index['measured_time']=now;(R/'source-index.json').write_text(json.dumps(index,indent=2)+'\n')
 print(bundle,'own_blocks',len(names),'own_bytes',len(aggregate.read_bytes()),'source_records',len(index['sources']),'literal_cuts',sum(len(x['cuts']) for x in index['sources']))
