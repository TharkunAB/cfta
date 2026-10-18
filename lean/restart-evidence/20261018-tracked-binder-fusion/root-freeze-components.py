import hashlib,json,re,runpy
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
checks=runpy.run_path(str(HERE/'verify-probes.py'))
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def write(name,value):(HERE/name).write_text(json.dumps(value,indent=2)+'\n')
reports={"tracked-slot":'# Fresh tracked lexical slots\n\nThe new related iff uses absence from both actual resolved root profiles.\npaired extends only the tracked list. Fixed captures and their free-name\nmap agreement stay exact. bind_marker uses explicit original lexical-name\nfreshness and binds the same new marker on both sides. No future-output\nabsence or body-comparison premise is used.\n\nThe actual source-built used Mu fixture compares an opaque replacement\nwith an untracked fallback. It extends the old relation and the lexical\nspine, then checks both literal marker executions. Production strict2\nand fixture strict6 have zero-byte logs. Canonical1 is warning-free.\nFull public3 and constructed1 checks pass. The reserved-name source error\nand five failed finite-computation fixture attempts remain preserved.\nNo Haskell bytes change. Full source binder closure is refuted under the\nold unrestricted contract by the separate binder-contract component.\n'}
for prefix,module,strict,canonical,kernels,count in [
 ('tracked-slot','SourceCurrentTrackedSlotExtension',2,1,6,3),
]:
 selection={'module':module,'strict':f'{prefix}-direct-{strict}','canonical':f'{prefix}-canonical-{canonical}',
  'constructed_strict':f'{prefix}-kernels-{kernels}',
  'groups':[{'name':prefix+'-public-1','pairs':count,'kind':'new-public','full_proof':True},
    {'name':prefix+'-kernels-public-1','pairs':1,'kind':'constructed','full_proof':True}]}
 for group in selection['groups']:checks['check_group'](group)
 for stem in [selection['strict'],selection['constructed_strict']]:
  receipt=json.loads((HERE/(stem+'.json')).read_text())
  assert receipt['exit_code']==0 and not (HERE/receipt['log']).read_bytes(),stem
  checks['check_limits'](stem)
 c=json.loads((HERE/(selection['canonical']+'.json')).read_text());log=(HERE/c['log']).read_text()
 assert c['exit_code']==0 and 'Build completed successfully' in log and not re.search(r'warning:|error:',log)
 checks['check_limits'](selection['canonical'])
 write(prefix+'-selection.json',selection)
 (HERE/(prefix+'-report.md')).write_text(reports[prefix])
 verifier='''import hashlib,json,re,runpy
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
prefix=PREFIX
read=lambda name:json.loads((HERE/name).read_text())
sha=lambda path:hashlib.sha256(path.read_bytes()).hexdigest()
for item in read(prefix+'-manifest.json')['entries']:
 assert sha(ROOT/item['path'])==item['sha256'],item['path']
s=read(prefix+'-selection.json');c=runpy.run_path(str(HERE/'verify-probes.py'))
for group in s['groups']:c['check_group'](group)
for stem in [s['strict'],s['constructed_strict']]:
 r=read(stem+'.json');assert r['exit_code']==0 and not (HERE/r['log']).read_bytes();c['check_limits'](stem)
r=read(s['strict']+'.json');assert (ROOT/'lean/MicroCFTA'/(s['module']+'.lean')).read_bytes()==(HERE/r['source']).read_bytes()
r=read(s['constructed_strict']+'.json');assert (HERE/(prefix+'-kernels.lean')).read_bytes()==(HERE/r['source']).read_bytes()
r=read(s['canonical']+'.json');log=(HERE/r['log']).read_text();assert r['exit_code']==0 and 'Build completed successfully' in log
assert not re.search(r'warning:|error:',log);c['check_limits'](s['canonical'])
print(json.dumps({'status':'PASS','public_pairs':sum(g['pairs'] for g in s['groups'] if g['kind']=='new-public'),'constructed_pairs':1,'pins':len(read(prefix+'-manifest.json')['entries'])}))
'''.replace('PREFIX',repr(prefix))
 (HERE/(prefix+'-verify.py')).write_text(verifier)
 dependencies=['SourceCurrentTrackedRootProfile','SourceCurrentTrackedFilteredFusion',module,
 'SourceCurrentReaderReplacementSlots','SourceCurrentNativeMuIssuedWriters',
 'SourceCurrentBinderFusionInduction','SourceCurrentPublicationSharedReplacements']
 if prefix=='tracked-writer':dependencies+=['SourceCurrentTrackedFilteredNodeFusion']
 paths=[ROOT/'lean/MicroCFTA'/(name+'.lean') for name in dependencies]
 paths += [p for p in HERE.glob(prefix+'-*') if p.is_file() and p.name!=prefix+'-manifest.json']
 paths += [HERE/name for name in ['root-run-check.py','root-capped-worker.py','verify-probes.py']]
 write(prefix+'-manifest.json',{'entries':[{'path':str(p.relative_to(ROOT)),'sha256':sha(p)} for p in sorted(set(paths))]})
 print(prefix,'frozen',len(set(paths)))
