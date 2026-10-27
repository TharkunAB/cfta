from pathlib import Path
import hashlib,json,datetime
root=Path('/home/tritlo/Code/mcfta');stage=Path('/tmp/mcfta-native-scan-coverage-20261027');a=stage/'head-owner'
def ident(b):return {'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
idx=json.loads((a/'source-index.json').read_text())
def cap(p,rel,cuts=()):
 b=p.read_bytes();dest=Path(rel);(a/dest).parent.mkdir(parents=True,exist_ok=True);(a/dest).write_bytes(b)
 r={'source':str(p),'whole':{'path':str(dest),**ident(b)},'cuts':[]};lines=b.splitlines(keepends=True)
 for first,last in cuts:
  cb=b''.join(lines[first-1:last]);cp=dest.parent/(dest.name+f'.L{first}-L{last}.txt');(a/cp).write_bytes(cb)
  r['cuts'].append({'path':str(cp),**ident(cb),'first_line':first,'last_line':last})
 idx['sources'].append(r)
checks=json.loads((stage/'strict-checks.json').read_text());mods=json.loads((stage/'modules.json').read_text())
for m in mods:
 p=root/'lean/MicroCFTA'/f'{m}.lean';b=p.read_bytes();r=json.loads((stage/checks[m]/'report.json').read_text())
 assert r['exit_code']==0 and r['bytes']==0 and r['source_sha256']==ident(b)['sha256']
 assert b==(stage/checks[m]/'MicroCFTA'/f'{m}.lean').read_bytes()
 lines=b.decode().splitlines();starts=[i+1 for i,l in enumerate(lines) if l.startswith('theorem ')]
 cuts=[(first,next(i+1 for i in range(first-1,len(lines)) if ':= by' in lines[i])) for first in starts]
 cap(p,f'final/sources/{m}.lean',cuts)
assert sum(len((root/'lean/MicroCFTA'/f'{m}.lean').read_bytes()) for m in mods)==49423
assert sum(len((root/'lean/MicroCFTA'/f'{m}.lean').read_text().splitlines()) for m in mods)==720
for name in ['source-validation.json','preservation-validation.json','public-validation.json','modules.json','strict-checks.json']:
 cap(stage/name,f'final/evidence/{name}')
for check in ['audit-1','strict-audit-1','public-readback-1']:
 r=json.loads((stage/check/'report.json').read_text());b=(stage/check/'raw.log').read_bytes()
 assert r['exit_code']==0 and ident(b)=={'bytes':r['bytes'],'sha256':r['sha256']}
 assert r['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
 for name in ['report.json','raw.log']:cap(stage/check/name,f'final/checks/{check}/{name}')
raw=(stage/'public-readback-1/raw.log').read_bytes();prior=(stage/'prior-public-readback/raw.log').read_bytes();new=(stage/'new-public-blocks.txt').read_bytes()
assert len(raw)==710226 and ident(raw)['sha256']=='9c4a8166b6236d4a7b0545c9391dfe9f604ecfdeef061a9b8485bf26f1913dcb'
assert len(prior)==667078 and raw[:len(prior)]==prior and raw[len(prior):]==new and len(new)==43148
lines=new.splitlines(keepends=True);starts=[i+1 for i,l in enumerate(lines) if l.startswith(b'MicroCFTA.')];assert len(starts)==3
cuts=[(first,starts[i+1]-1 if i+1<len(starts) else len(lines)) for i,first in enumerate(starts)]
cap(stage/'new-public-blocks.txt','final/public/new-public-blocks.txt',cuts)
cap(stage/'public-readback-1/public.lean','final/public/public.lean')
(a/'source-index.json').write_text(json.dumps(idx,indent=2)+'\n')
(a/'final-public-review.json').write_text(json.dumps({'status':'CLEAR','reviewed_at':datetime.datetime.now().astimezone().isoformat(),'complete_new_public_blocks_read':3,'new_blocks':ident(new),'public_raw':ident(raw),'prior_prefix':ident(prior),'prior_prefix_literal_equal':True,'installed_modules_match_actual_strict_sources':True,'new_definitions':0,'new_structures':0,'standard_axioms_only':['propext','Classical.choice','Quot.sound'],'Audit':{'jobs':4248,'theorem_dependencies':80083},'scope':'Actual NativeBranches accepting indexed receipt under supported original prefix; semantic-facing parent wrapper adds all-selected support and proves exact scan completion. Separate recursive hook stops and recursive rendering coverage remain open.','state':'OPEN; final documentation/seal cue pending'},indent=2)+'\n')
p=a/'report.txt';s=p.read_text();s+='''\nFinal source/public checks (OPEN for prose)\nAll THREE complete new public signature/axiom blocks were read, 554 lines and 43148 bytes. All three installed sources match their actual successful strict snapshots. The full public readback is 710226 bytes, SHA256 9c4a8166b6236d4a7b0545c9391dfe9f604ecfdeef061a9b8485bf26f1913dcb; its whole prior 667078-byte/173-block prefix is independently literal-equal. The final modules contain 720 lines, 49423 bytes and three theorems, with no definitions or structures. Aggregate Audit passes 4248 jobs and checks 80083 dependencies. Standalone Audit passes with the expected 56-byte count line. The earlier dependency warning remains in exact Lake output. Preservation-validation records 93 prior strong sources, 440 enumeration sources and 203 Haskell sources unchanged; Audit only adds three imports. Root's final standard-axiom and no-elision validation is retained with whole public output and all three full public cuts. All source/packet/quantifier reviews are CLEAR; source head, documentation and final seal remain pending. No compiler or build was run by this worker.\n''';p.write_text(s)
print(json.dumps({'review':'CLEAR / OPEN','source_records':len(idx['sources']),'literal_cuts':sum(len(r['cuts']) for r in idx['sources']),'new_public_cuts':cuts},indent=2))
