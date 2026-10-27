from pathlib import Path
import hashlib,json,subprocess
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-template-coverage-20261027');review=area/'root-source-review';review.mkdir()
def digest(data):return hashlib.sha256(data).hexdigest()
sources=[]
modules=json.loads((area/'modules.json').read_text())
for module in modules:
 p=root/'lean/MicroCFTA'/(module+'.lean');b=p.read_bytes();q=review/'sources'/p.name;q.parent.mkdir(exist_ok=True);q.write_bytes(b)
 sources.append(dict(source=str(p),whole=dict(path=str(q.relative_to(review)),bytes=len(b),sha256=digest(b)),cuts=[],review_scope='Whole final source read through initial whole text and all exact version deltas. Actual failed check lineage retained.'))
for name in ['new-public-blocks.txt','root-contract-comparisons.json','public-prefix-comparison.json','source-validation.json','preservation-validation.json']:
 p=area/name;b=p.read_bytes();q=review/'sources'/name;q.write_bytes(b);sources.append(dict(source=str(p),whole=dict(path=str(q.relative_to(review)),bytes=len(b),sha256=digest(b)),cuts=[],review_scope='Whole new public text or validation record read. Final public delta read in full.'))
p=root/'lean/notes-current-template-coverage.md';b=p.read_bytes();q=review/'sources'/p.name;q.write_bytes(b);sources.append(dict(source=str(p),whole=dict(path=str(q.relative_to(review)),bytes=len(b),sha256=digest(b)),cuts=[],review_scope='Whole new note read.'))
for r in json.loads((area/'document-validation.json').read_text()):
 if 'inserted_bytes' not in r:continue
 p=root/r['path'];b=p.read_bytes();old=(area/'prior-documents'/r['path']).read_bytes();offset=r['offset'];end=offset+r['inserted_bytes'];assert b[:offset]+b[end:]==old;ins=b[offset:end];q=review/'insertions'/(r['path'].replace('/','__')+'.txt');q.parent.mkdir(exist_ok=True);q.write_bytes(ins)
 first=len(b[:offset].splitlines())+1;last=first+len(ins.splitlines())-1
 sources.append(dict(source=str(p),source_bytes=len(b),source_sha256=digest(b),reconstruction=dict(prior=dict(path=str(area/'prior-documents'/r['path']),bytes=len(old),sha256=digest(old)),insert=dict(path=str(q),bytes=len(ins),sha256=digest(ins)),offset=offset),cuts=[dict(path=str(q.relative_to(review)),bytes=len(ins),sha256=digest(ins),first_line=first,last_line=last)],review_scope='Only exact current insertion read. Whole older body preserved by inverse.'))
(review/'source-index.json').write_text(json.dumps(dict(sources=sources),indent=2)+'\n')
commands=[]
for p in sorted(area.glob('*/report.json')):
 r=json.loads(p.read_text());b=(p.parent/'raw.log').read_bytes();assert len(b)==r['bytes'] and digest(b)==r['sha256'];assert r['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'};commands.append(dict(name=p.parent.name,report=r))
assert len(commands)==48 and sum(r['report']['exit_code']!=0 for r in commands)==18
(area/'actual-commands.json').write_text(json.dumps(commands,indent=2)+'\n')
(area/'current-document-changes.patch').write_bytes(subprocess.check_output(['git','diff','--',*json.loads((area/'document-paths.json').read_text())],cwd=root))
(review/'report.md').write_text('''# Root final source review

All eleven final proof modules, sixteen complete new public theorem statements
and five printed semantic definitions were read. The final universal observer
change was read in the complete exact public delta. All earlier 233 blocks
remain the exact 971561-byte prefix. Only standard axioms occur.

The actual matcher preserves original template meaning under assignment
completion. Truncation admits any complete term. Actual partial rendering
threads the same original assignment through compression and stored equations.
Original catalog membership and ProgramAt locate each started match. Encoded
constant/application syntax justifies structural arrow-marker erasure.
Actual pending resumption, all ordered group reads, early and idle paths,
finishChecks and recordTypes preserve original semantic refutation.

The callback wrapper retains exact original admission and the entire original
return conjunction. The original producer is called once. Its fixed fuel,
result and final state precede every semantic language, meaning, assignment
and antecedent. New original semantic conditions imply false and retained
refutation for the SAME result. No desired future execution, false flag,
final model or pre-assumed callback success is an admission premise.

Recursive origin/preservation of these conditions remains open. ProgramEncoding
is not derived from arbitrary packets or public API construction. Avoids is a
forbidden-template policy; native acceptance alone does not supply it. Whole
recursive coverage, discharge/render coverage, policy/frontier/projection and
physical Haskell correspondence remain open. Prior exact finite pruning,
conditional output soundness, emitted-cache Proper and chosen invocation or
exact earlier stop retain their scopes.

All 48 actual commands and 18 failures remain. Every failed proof/probe raw
log was read before repair. Uncompiled intermediate drafts are labeled.
The copied recursive converter approach was rejected. Final actual-helper
macros produce checked references, not an alternate runtime converter. The
public helper definition-boundary correction caused no proof rerun. Audit
and public checks repeated for the strengthened final theorem declaration.

All final strict checks and Audit pass. Full Audit has 4293 jobs and checks
80301 theorem dependencies. All actual commands are serial measured 4 GiB
memory.max/high with swap0. No warning or heartbeat suppression is added.
All 4281 old non-Audit Lean sources, 130 strong modules and 791 tracked
Haskell source/evidence files retain bytes. No Haskell edit/test/benchmark.

The complete new note and all nine exact current document insertion bodies
were read. The eight common insertions are byte-identical; FINDINGS adds the
source-encoding assessment and previous LPO/KBO repaired status. All whole
older document bodies are preserved by inverse. No whole-file reading claim
is made for the giant historical documents. Previous evidence stays frozen.
Three independent bounded reviews seal their own complete evidence trees.
Goal ACTIVE. This checkpoint is progress, not whole-goal completion.
''')
print(json.dumps(dict(status='pass',root_source_records=len(sources),commands=len(commands),failures=18)))
