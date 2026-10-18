import hashlib,json,re,runpy
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
checker=runpy.run_path(str(HERE/'verify-probes.py'))
def write(name,value):
 (HERE/name).write_text(json.dumps(value,indent=2)+'\n')
for prefix,module,strict,kernels,public_count in [
 ('bounded-base','SourceCurrentBoundedFilteredFusion',2,2,5),
 ('bounded-writer','SourceCurrentBoundedWriterFusion',2,2,2),
]:
 selection={'module':module,'strict':f'{prefix}-direct-{strict}','canonical':f"{prefix}-canonical-{2 if prefix=='bounded-writer' else 1}",
  'constructed_strict':f'{prefix}-kernels-{kernels}',
  'groups':[{'name':f"{prefix}-public-{2 if prefix=='bounded-writer' else 1}",'pairs':public_count,'kind':'new-public','full_proof':True},
   {'name':prefix+'-kernels-public-1','pairs':1,'kind':'constructed','full_proof':True}]}
 for group in selection['groups']:checker['check_group'](group)
 for stem in [selection['strict'],selection['constructed_strict']]:
  receipt=json.loads((HERE/(stem+'.json')).read_text())
  assert receipt['exit_code']==0 and not (HERE/receipt['log']).read_bytes()
  checker['check_limits'](stem)
 write(prefix+'-selection.json',selection)
 text={
 'bounded-base': """# Fusion at an original raw depth bound

The new contract is the prior reader-filtered Fusion contract restricted
to two original raw values whose depths are at most bound. Replacement
values, outputs and source syntax remain unrestricted. of_fusion embeds
the earlier unbounded law. mono restricts a larger bound. Empty and variable
source cases satisfy every bound. No recursive induction is assumed here.

The actual variable integration uses raw reference depths0. Its first
resolved value is a used source-built Mu with depth1. The second is a
bare nonempty ordinary reference. The bounded variable law derives equal
physical Empty. Original and reconstructed depths are explicitly distinct.

Production strict2 and constructed strict2 have literal empty logs.
Canonical1 is warning-free. Full public5 and constructed1 checks pass.
Prior arithmetic/fixture tactic failures remain preserved. General binder
fusion and implementation correspondence remain open. No Haskell changes.
""",
 'bounded-writer': """# Smaller-depth fusion at actual writer callbacks

publication derives complete original lexical reader Contexts and actual
warm raw/filter calls from historical callback verification and Keeps.
Actual deterministic callback calls align original depth certificates.
It applies a source Fusion law at event.body.depth to those original raws.
Both complete replacement maps use a shared map. Cross-absence retains
both actual sparse stored calls. Outer replacements can contain Empty.
Only local physical Empty agreement is needed.

writer recovers the exact earlier event from strong Written. It derives
cut and body Keeps from actual reservation, body path and issued suffix.
It consumes the uniform source induction hypothesis strictly below the
selected original Mu depth. That uniform hypothesis remains unproved.
The conclusion compares unlowered callback Empty tests. It does not prove
whole open-Mu Empty or general binder Fusion.

The source-built writer integration uses node[var0,var1] and a captured
issued reference. Its outer map resolves that used capture to Empty. A
real source call prepares the dead edge at a later common reader. Both
local replacements are the available nonempty selected Mu. Both original
sparse stored calls are warm and return Empty. BinderFree derives the
bounded source-body law; no desired callback comparison is assumed.

Final production strict2 and fixture strict2 have literal empty logs.
Canonical2 is warning-free. Full public2 and constructed1 checks pass.
Independent review found a redundant instance linter warning in strict1
and canonical1. It was removed. Those earlier receipts remain unselected.
The first fixture proof errors remain preserved. No Haskell changes.
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
 dependencies=['SourceCurrentBoundedFilteredFusion','SourceCurrentNativeMuIssuedHistory',
 'SourceCurrentNativeMuIssuedWriters','SourceCurrentBinderFusionInduction',
 'SourceCurrentPublicationSharedReplacements','SourceCurrentUsedBinderAliasTransport',
 'SourceCurrentFilteredSourceFusion',module]
 paths=[ROOT/'lean/MicroCFTA'/(name+'.lean') for name in dependencies]
 paths += [p for p in HERE.glob(prefix+'-*') if p.is_file() and p.name!=prefix+'-manifest.json' and not p.name.startswith(prefix+'-review')]
 paths += [HERE/name for name in ['root-run-check.py','root-capped-worker.py','verify-probes.py']]
 write(prefix+'-manifest.json',{'entries':[{'path':str(p.relative_to(ROOT)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in sorted(set(paths))]})
 print(prefix,'frozen',len(set(paths)))
