import hashlib,json,re,runpy
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
checker=runpy.run_path(str(HERE/'verify-probes.py'))
def write(name,value):
 (HERE/name).write_text(json.dumps(value,indent=2)+'\n')
for prefix,module,strict,kernels,public_count in [
 ('issued-history','SourceCurrentNativeMuIssuedHistory',2,2,8),
 ('issued-writers','SourceCurrentNativeMuIssuedWriters',4,1,7),
]:
 selection={'module':module,'strict':f'{prefix}-direct-{strict}','canonical':f'{prefix}-canonical-1',
  'constructed_strict':f'{prefix}-kernels-{kernels}',
  'groups':[{'name':f'{prefix}-public-1','pairs':public_count,'kind':'new-public','full_proof':True},
   {'name':prefix+'-kernels-public-1','pairs':1,'kind':'constructed','full_proof':True}]}
 for group in selection['groups']:checker['check_group'](group)
 for stem in [selection['strict'],selection['constructed_strict']]:
  receipt=json.loads((HERE/(stem+'.json')).read_text())
  assert receipt['exit_code']==0 and not (HERE/receipt['log']).read_bytes()
  checker['check_limits'](stem)
 write(prefix+'-selection.json',selection)
 text={
 'issued-history': """# Issued-name retention on actual source paths

Path records NoNewMu, table growth and issued-name extension at each
retained effect. Actual build, buildMany and buildEdges derive these
receipts at every stopping state, including pending callback stops.
Publication follows the exact callback paths and actual reservation.
Path.issued derives complete forward issued-name retention. Path.forget
recovers the existing growth history. Old Grows and Path remain unchanged.

The actual source fixture first allocates a leaf. A later raw Mu receives
that leaf reference as an unused lexical capture. It derives the rich
path from empty, retains the unused reference, and forgets to the old path.
Production strict2 and fixture strict2 have literal empty logs. Canonical
and full public8/constructed1 checks pass. Earlier attempts remain.

This result does not derive final Ready, general binder fusion or Haskell
correspondence. No Haskell file is changed.
""",
 'issued-writers': """# Earlier selected writers retain issued-name suffixes

Written retains the exact first publication, its actual callback paths,
and both table growth and issued-name extension to the final reader.
Recovery follows the actual selected record. Existing old-history writer
contracts remain unchanged. Final Ready is an explicit input.

Written.raw_contexts derives both complete original lexical contexts at
that reader. It retains both historical raw source/filter pairs and their
literal warm replays. It uses actual source and filter issued-name facts.
No caller supplies reader lexical availability or a desired output law.

The actual source fixture includes an unused issued capture. It recovers
the writer from the final resident record and invokes raw_contexts.
Production strict4 and fixture strict1 have literal empty logs. Canonical
and full public7/constructed1 checks pass. Earlier attempts remain.
Independent review finds no material issue. General body/probe Empty
fusion and changing-capture observations remain open. No Haskell changes.
"""}[prefix]
 (HERE/(prefix+'-report.md')).write_text(text)
 verifier='''import hashlib,json,re,runpy
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
prefix=PREFIX
read=lambda name:json.loads((HERE/name).read_text())
sha=lambda path:hashlib.sha256(path.read_bytes()).hexdigest()
for item in read(prefix+'-manifest.json')['entries']:
 assert sha(ROOT/item['path'])==item['sha256'],item['path']
s=read(prefix+'-selection.json')
c=runpy.run_path(str(HERE/'verify-probes.py'))
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
 dependencies=['SourceCurrentNativeMuIssuedHistory','SourceCurrentNativeMuIssuedWriters',
 'SourceCurrentNativeMuGrowthHistory','SourceCurrentNativeMuGrowthWriters',
 'SourceCurrentNativeMuGrowthExecution','SourceCurrentNativeMuPublicationCallbacks',
 'SourceCurrentGeneratedHistoricalContext','SourceEqualityRequiredCache',module]
 paths=[ROOT/'lean/MicroCFTA'/(name+'.lean') for name in dependencies]
 paths += [p for p in HERE.glob(prefix+'-*') if p.is_file() and p.name!=prefix+'-manifest.json' and not p.name.startswith(prefix+'-review')]
 paths += [HERE/name for name in ['root-run-check.py','root-capped-worker.py','verify-probes.py']]
 write(prefix+'-manifest.json',{'entries':[{'path':str(p.relative_to(ROOT)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in sorted(set(paths))]})
 print(prefix,'frozen',len(set(paths)))
