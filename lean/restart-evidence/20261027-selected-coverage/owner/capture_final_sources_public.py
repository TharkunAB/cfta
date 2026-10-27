from pathlib import Path
import json,hashlib,datetime,re
root=Path('/home/tritlo/Code/mcfta');stage=Path('/tmp/mcfta-selected-coverage-20261027');a=stage/'owner'
def ident(b):return {'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
index=json.loads((a/'source-index.json').read_text())
def capture(p,snapshot,cuts=()):
 b=p.read_bytes();sp=Path(snapshot);(a/sp).parent.mkdir(parents=True,exist_ok=True);(a/sp).write_bytes(b)
 r={'source':str(p),'snapshot':str(sp),**ident(b),'cuts':[]};lines=b.splitlines(keepends=True)
 for first,last in cuts:
  cb=b''.join(lines[first-1:last]);cp=sp.parent/(sp.name+f'.L{first}-L{last}.txt');(a/cp).write_bytes(cb)
  r['cuts'].append({'snapshot':str(cp),'first_line':first,'last_line':last,**ident(cb),'source_sha256':r['sha256']})
 index['sources'].append(r);return r
modules=json.loads((stage/'modules.json').read_text());checks=json.loads((stage/'strict-checks.json').read_text())
for m in modules:
 p=root/'lean/MicroCFTA'/f'{m}.lean';b=p.read_bytes();report=json.loads((stage/checks[m]/'report.json').read_text())
 assert report['exit_code']==0 and report['bytes']==0 and report['source_sha256']==ident(b)['sha256']
 assert b==(stage/checks[m]/'MicroCFTA'/f'{m}.lean').read_bytes()
 lines=b.decode().splitlines(); starts=[i+1 for i,x in enumerate(lines) if x.startswith('theorem ')]
 cuts=[]
 for first in starts:
  end=next(i+1 for i in range(first-1,len(lines)) if ':= by' in lines[i]);cuts.append((first,end))
 capture(p,f'final/sources/{m}.lean',cuts)
 if m=='SourcePruningEnumerationSelectedEdgeCoverage':assert b==(a/'drafts/v3/SourcePruningEnumerationSelectedEdgeCoverage.lean').read_bytes()
 for q in ['report.json','raw.log']:
  capture(stage/checks[m]/q,f'final/strict/{checks[m]}/{q}')
for name in ['modules.json','strict-checks.json','source-validation.json','public-validation.json','source-commit-accepting-audit.json','source-commit-coverage.json']:
 capture(stage/name,f'final/evidence/{name}')
for check in ['audit-coverage-1','strict-audit-coverage-1','public-readback-1']:
 rp=stage/check/'report.json';report=json.loads(rp.read_text());raw=(stage/check/'raw.log').read_bytes()
 assert report['exit_code']==0 and report['bytes']==len(raw) and report['sha256']==ident(raw)['sha256']
 assert report['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
 capture(rp,f'final/checks/{check}/report.json');capture(stage/check/'raw.log',f'final/checks/{check}/raw.log')
public=(stage/'public-readback-1/raw.log').read_bytes();prior=(stage/'prior-public-readback/raw.log').read_bytes();new=(stage/'new-public-blocks.txt').read_bytes()
assert len(prior)==592943 and public[:len(prior)]==prior and public[len(prior):]==new
lines=new.splitlines(keepends=True);starts=[i+1 for i,line in enumerate(lines) if line.startswith(b'MicroCFTA.')]
assert len(starts)==5
cuts=[(first,(starts[i+1]-1 if i+1<len(starts) else len(lines))) for i,first in enumerate(starts)]
capture(stage/'new-public-blocks.txt','final/public/new-public-blocks.txt',cuts)
capture(stage/'public-readback-1/public.lean','final/public/public.lean')
(a/'source-index.json').write_text(json.dumps(index,indent=2)+'\n')
(a/'final-public-review.json').write_text(json.dumps({'status':'CLEAR','reviewed_at':datetime.datetime.now().astimezone().isoformat(),'source_head':'bcd40a836d8b1ae4d388fecf0f1ca81a27cbb673','complete_new_blocks_read':5,'public':ident(public),'new_blocks':ident(new),'prior_prefix':ident(prior),'prior_prefix_literal_equal':True,'all_current_installed_modules_match_actual_strict_source':True,'standard_axioms_only':['propext','Quot.sound','Classical.choice'],'new_definitions':0,'new_data_structures':0,'notes':'Primary old-packet wrapper chooses bounds before models. accepted_complete takes a model before its existential bounds and derives actual projection+inherited arity. Whole recursive selector coverage, rendering completeness and physical correspondence remain open. No publication/archive verification is asserted.'},indent=2)+'\n')
print(json.dumps({'records':len(index['sources']),'cuts':sum(len(x['cuts']) for x in index['sources']),'public_blocks':cuts},indent=2))
