from pathlib import Path
import hashlib,json,datetime
root=Path('/home/tritlo/Code/mcfta');stage=Path('/tmp/mcfta-selector-capture-20261027');a=stage/'captured-owner'
def ident(b):return {'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
idx=json.loads((a/'source-index.json').read_text())
def cap(p,dest,cuts=()):
 b=p.read_bytes();d=Path(dest);(a/d).parent.mkdir(parents=True,exist_ok=True);(a/d).write_bytes(b)
 rec={'source':str(p),'whole':{'path':str(d),**ident(b)},'cuts':[]};lines=b.splitlines(keepends=True)
 for first,last in cuts:
  cb=b''.join(lines[first-1:last]);cp=d.parent/(d.name+f'.L{first}-L{last}.txt');(a/cp).write_bytes(cb)
  rec['cuts'].append({'path':str(cp),**ident(cb),'first_line':first,'last_line':last})
 idx['sources'].append(rec)
checks=json.loads((stage/'strict-checks.json').read_text())
for m in json.loads((stage/'modules.json').read_text()):
 p=root/'lean/MicroCFTA'/f'{m}.lean';b=p.read_bytes();r=json.loads((stage/checks[m]/'report.json').read_text())
 assert r['source_sha256']==ident(b)['sha256'] and r['exit_code']==0 and r['bytes']==0
 assert b==(stage/checks[m]/'MicroCFTA'/f'{m}.lean').read_bytes()
 lines=b.decode().splitlines();starts=[i+1 for i,l in enumerate(lines) if l.startswith('theorem ')]
 cuts=[(first,next(i+1 for i in range(first-1,len(lines)) if ':= by' in lines[i])) for first in starts]
 cap(p,f'final/sources/{m}.lean',cuts)
 if m=='SourcePruningEnumerationSelectorLanguage':
  for q in ['report.json','raw.log']:
   cap(stage/checks[m]/q,f'final/checks/{checks[m]}/{q}')
for name in ['source-validation.json','public-validation.json','preservation-validation.json','modules.json','strict-checks.json']:
 cap(stage/name,f'final/evidence/{name}')
for check in ['audit-1','strict-audit-1','public-readback-1']:
 r=json.loads((stage/check/'report.json').read_text());b=(stage/check/'raw.log').read_bytes()
 assert r['exit_code']==0 and ident(b)=={'bytes':r['bytes'],'sha256':r['sha256']}
 assert r['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
 for name in ['report.json','raw.log']:
  cap(stage/check/name,f'final/checks/{check}/{name}')
raw=(stage/'public-readback-1/raw.log').read_bytes();prior=(stage/'prior-public-readback/raw.log').read_bytes();new=(stage/'new-public-blocks.txt').read_bytes()
assert len(raw)==667078 and ident(raw)['sha256']=='4453ff071f4251bd7b753e880e0301ccdc5c1eed804c34a416d7fece799ee2a5'
assert len(prior)==630571 and raw[:len(prior)]==prior and raw[len(prior):]==new and len(new)==36507
lines=new.splitlines(keepends=True);starts=[i+1 for i,l in enumerate(lines) if l.startswith(b'MicroCFTA.')];assert len(starts)==5
cuts=[(first,starts[i+1]-1 if i+1<len(starts) else len(lines)) for i,first in enumerate(starts)]
cap(stage/'new-public-blocks.txt','final/public/new-public-blocks.txt',cuts)
cap(stage/'public-readback-1/public.lean','final/public/public.lean')
(a/'source-index.json').write_text(json.dumps(idx,indent=2)+'\n')
(a/'final-public-review.json').write_text(json.dumps({'status':'CLEAR','reviewed_at':datetime.datetime.now().astimezone().isoformat(),'complete_new_public_blocks_read':5,'new_blocks':ident(new),'public_raw':ident(raw),'prior_public_prefix':ident(prior),'literal_prior_prefix_equal':True,'installed_module_bytes_match_actual_strict_sources':True,'standard_axioms_only':['propext','Classical.choice','Quot.sound'],'printed_definitions':0,'new_structures':0,'aggregate_Audit':{'jobs':4245,'theorem_dependencies':80074},'claims':'Permutation selector retains an accepting resident witness. Parent model derives a chosen actual captured completion. Ordered-scan reachability, continuation coverage, recursive coverage and concrete rendering coverage remain open.','state':'OPEN; final documentation and seal cue pending'},indent=2)+'\n')
p=a/'report.txt';s=p.read_text();s+='''\nFinal compiler/public evidence (OPEN for prose)\nAll five complete NEW signature/axiom blocks were read: 469 lines, 36507 bytes. The installed selector, captured primary and captured parent wrapper bytes match their successful strict source snapshots. Public output is 667078 bytes, SHA256 4453ff071f4251bd7b753e880e0301ccdc5c1eed804c34a416d7fece799ee2a5, with the entire earlier 630571-byte/168-block prefix literally equal. New output contains five theorem blocks; no definition or structure is added, and only propext, Classical.choice and Quot.sound occur. Aggregate Audit passes 4245 jobs and checks 80074 dependencies; the known old dependency warning remains in its exact raw output. Standalone strict Audit passes with its expected 56-byte dependency-count line. Source-validation records final strict checks; preservation-validation records 437 existing enumeration sources and 203 Haskell sources unchanged. No compiler was run by this worker. Exact whole raw output, strict/build reports and five public cuts are retained. Final source checkpoint/docs and archive/publication remain to be bound; this bundle stays OPEN.\n''';p.write_text(s)
print(json.dumps({'records':len(idx['sources']),'literal_cuts':sum(len(r['cuts']) for r in idx['sources']),'public_cuts':cuts,'review':'CLEAR / OPEN'},indent=2))
