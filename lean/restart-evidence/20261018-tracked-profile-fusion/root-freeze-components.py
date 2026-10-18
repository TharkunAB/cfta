import hashlib,json,re,runpy
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
checks=runpy.run_path(str(HERE/'verify-probes.py'))
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def write(name,value):(HERE/name).write_text(json.dumps(value,indent=2)+'\n')
reports={
 'tracked-root':'''# Finite tracked root profiles

mask retains a pure root-reference profile exactly when all its names
are tracked. Every other nonempty profile is opaque. Related compares
these observations up to name order and duplicates. It preserves physical
Empty and bare tracked names for actual available normalized results.
It does not claim full language equivalence. nil_equiv recovers the exact
earlier Empty-only observation. mask_cons_fresh uses absence from the
actual pure profile; it does not infer future-result freshness.

The actual fixture builds a used resident Mu. Its opaque observation agrees
with an untracked bare reference and differs from a tracked bare reference.
It checks nil masking and fresh-marker extension. Production strict6 and
fixture strict1 have zero-byte logs. Canonical5 is warning-free. Full public14
and constructed1 groups pass complete proof and standard-axiom checks.
Earlier source errors and linter-warning attempts remain unselected.
''',
 'tracked-base':'''# Tracked filtered Fusion and exact prior-contract recovery

Fusion retains the earlier bounded source contract. Both original raw
values have depths at most bound. Replacements and reconstructed results
remain unrestricted. Reference slots and outputs compare Related markers.
All historical Contexts, actual warm source/filter/execute calls, live
Aliases, self tests, Replacements, availability and growth remain.

empty and reference prove the base cases. to_empty derives exactly the
previous bounded Fusion under its original Paired Empty premise. It derives
filtered and executed output availability from actual completed calls.
Unused lexical references need no new reader-availability hypothesis.
The source-built variable fixture compares a used Mu with an untracked
fallback reference, then applies to_empty under the old Paired Empty data.

Production strict4 and fixture strict1 have zero-byte logs. Canonical3
is warning-free. Full public4 and constructed1 groups pass. Earlier errors
and linter-warning attempts remain preserved. General binder Fusion stays
open. No Haskell bytes change.
''',
 'tracked-writer':'''# Actual earlier-writer tracked callback comparison

publication derives both complete lexical reader Contexts and literal
warm raw/filter calls from an actual Publication and Keeps suffixes.
Original raw depth certificates instantiate Fusion at event.body.depth.
A shared map retains both original sparse execute calls. Outer maps may
contain Empty. Related local replacements derive Related callback results.
writer recovers the exact earlier issued writer, its syntax and captures.
It consumes a uniform source induction hypothesis at strictly smaller
original body depth. That hypothesis is explicit and unproved.

The constructed source-built writer uses node[var0,var1]. An actual outer
capture resolves to Empty. Both nonempty local replacements are the
selected candidate Mu. A real later source call prepares the dead row.
The tracked node and variable lemmas derive this particular body Fusion.
The witness applies publication, not the unproved uniform writer IH.

Production strict1 and fixture strict2 have zero-byte logs. Canonical1 is
warning-free. Full public2 and constructed1 groups pass. The first fixture
list-membership tactic error and warning remain unselected. No production
or Haskell repair was needed. Full binder Fusion and outer lower remain open.
'''}
for prefix,module,strict,canonical,kernels,count in [
 ('tracked-root','SourceCurrentTrackedRootProfile',6,5,1,14),
 ('tracked-base','SourceCurrentTrackedFilteredFusion',4,3,1,4),
 ('tracked-writer','SourceCurrentTrackedWriterFusion',1,1,2,2),
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
 'SourceCurrentBoundedFilteredFusion','SourceCurrentNativeMuIssuedWriters',
 'SourceCurrentBinderFusionInduction','SourceCurrentPublicationSharedReplacements']
 if prefix=='tracked-writer':dependencies+=['SourceCurrentTrackedFilteredNodeFusion']
 paths=[ROOT/'lean/MicroCFTA'/(name+'.lean') for name in dependencies]
 paths += [p for p in HERE.glob(prefix+'-*') if p.is_file() and p.name!=prefix+'-manifest.json']
 paths += [HERE/name for name in ['root-run-check.py','root-capped-worker.py','verify-probes.py']]
 write(prefix+'-manifest.json',{'entries':[{'path':str(p.relative_to(ROOT)),'sha256':sha(p)} for p in sorted(set(paths))]})
 print(prefix,'frozen',len(set(paths)))
