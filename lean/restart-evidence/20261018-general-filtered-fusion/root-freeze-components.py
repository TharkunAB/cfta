import hashlib,json,re,runpy
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
checker=runpy.run_path(str(HERE/'verify-probes.py'))
def write(name,value):
 (HERE/name).write_text(json.dumps(value,indent=2)+'\n')
for prefix,module,strict,kernels,public_count in [
 ('node-fusion','SourceCurrentFilteredNodeFusion',3,4,2),
 ('binder-free','SourceCurrentFilteredBinderFreeFusion',7,2,1),
]:
 selection={'module':module,'strict':f'{prefix}-direct-{strict}','canonical':f'{prefix}-canonical-1',
  'constructed_strict':f'{prefix}-kernels-{kernels}',
  'groups':[{'name':f'{prefix}-public-1','pairs':public_count,'kind':'new-public','full_proof':True},
   {'name':prefix+'-kernels-public-'+('2' if prefix=='node-fusion' else '1'),'pairs':1,'kind':'constructed','full_proof':True}]}
 for group in selection['groups']:checker['check_group'](group)
 for stem in [selection['strict'],selection['constructed_strict']]:
  receipt=json.loads((HERE/(stem+'.json')).read_text())
  assert receipt['exit_code']==0 and not (HERE/receipt['log']).read_bytes()
  checker['check_limits'](stem)
 write(prefix+'-selection.json',selection)
 text={
 'node-fusion':'''# Node fusion with resolved Empty slots

Actual indexed historical source rows and actual stored child calls derive
opposite stored-row survival. Strict source child Fusion gives ordered
physical Empty agreement. Full symbols and guards are retained. The node
endpoint derives the complete reader-filtered Fusion law. It needs only
Paired resolved Empty tests, rather than lexical Generated memberships.
No desired parent law or whole lexical availability at the reader is used.
Fresh child self-filter names are absent by selected raw availability.

The actual integration has distinct raw source parents with uninterned
references 0 and 1. Both references resolve to Empty. Row 9 disappears;
rows 10 and 11 survive. A real earlier source seed allocated the dead edge,
so both final stored calls are warm. The same actual seed result is returned.
Contexts, Ready, raw availability, maps, Paired, aliases and scoped self
tests are derived. The public node endpoint is applied to strict child laws.

Production strict3 has a literal empty log. Strict1 failed to connect to
the required scope bus. Strict2 retains declaration-name warnings. The
canonical build is clean. Fixture strict4 has a literal empty log. Earlier
fixture attempts remain. The first full fixture probe terminated with -15
during printing; no cause is established. The final public alias retains
the same full statement and checked private proof. Full public2 and
constructed1 probes pass all printer settings and standard axioms.

The result does not establish arbitrary source binder fusion or child
record equality. No Haskell file is changed.
''',
 'binder-free':'''# Complete binder-free source fusion

Explicit strong induction on source syntax composes the empty, variable,
node and union cases. Every immediate source child is smaller. Existing
BinderFree, ManyBinderFree and EdgesBinderFree define the exact fragment.
No new source binder expression is permitted. Fixed supplied captures can
contain arbitrary open nested Mu values; the common Fusion slot contract
requires equal replacement maps on each fixed capture's free support.

The new theorem yields the full actual reader-filtered Fusion statement.
Raw source Contexts remain at their original historical points. Filters
and stored calls run warm at the reader. Resolved varying reference slots
need only equal physical Empty tests. No general output law is assumed.

The actual integration applies the complete source endpoint to the same
changing-reference node execution. Both distinct parents reconstruct to
the actual two-row seed output. All initial facts and calls are derived.

Production strict7 and fixture strict2 have literal empty logs. Canonical
and full public1/constructed1 probes pass. Earlier failed induction and
fixture attempts remain unselected. General source binder fusion,
changing-capture observations and recursive completion remain open.
No Haskell file is changed.
'''}[prefix]
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
 dependencies=['SourceCurrentFilteredSourceFusion','SourceCurrentFilteredNodeFusion','SourceCurrentFilteredUnionFusion',module,
 'SourceCurrentGeneratedNodeSchedules','SourceCurrentGeneratedNodeEmpty','SourceCurrentStoredLiteralExecutionParts',
 'SourceCurrentFilteredUnionCoverage','SourceCurrentReaderReplacementSlots','InternedStoredShallowCompletion']
 paths=[ROOT/'lean/MicroCFTA'/(name+'.lean') for name in dependencies]
 paths += [p for p in HERE.glob(prefix+'-*') if p.is_file() and p.name!=prefix+'-manifest.json' and not p.name.startswith(prefix+'-review')]
 paths += [HERE/name for name in ['root-run-check.py','root-capped-worker.py','verify-probes.py']]
 write(prefix+'-manifest.json',{'entries':[{'path':str(p.relative_to(ROOT)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in sorted(set(paths))]})
 print(prefix,'frozen',len(set(paths)))
