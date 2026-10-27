from pathlib import Path
import json,hashlib,re
repo=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-flat-recursive-20261027');out=area/'finite-callback-draft';sha=lambda b:hashlib.sha256(b).hexdigest()
def put(rel,b):p=out/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
def js(rel,x):put(rel,(json.dumps(x,indent=2)+'\n').encode())
inputs=[repo/'lean/MicroCFTA'/f'{name}.lean' for name in ['SourcePruningEnumerationFiniteCallbackResources','SourcePruningEnumerationRecursiveCallback','SourcePruningEnumerationSuspendedMass','SourceFlatPruningContinuation','SourceFlatPruningOracle','SourceFlatPruningRecursive']]+[area/'finite-contract-draft/SourceFlatPruningFiniteContract.lean']
sources=[];cuts=[]
for p in inputs:
 b=p.read_bytes();dest='inputs/'+p.name;put(dest,b);sources.append(dict(path=str(p),source=str(p),snapshot=dest,bytes=len(b),sha256=sha(b),read_scope='actual API and original proof induction reviewed'))
for p,start,end in [(inputs[0],38,81),(inputs[1],29,60),(inputs[2],89,95),(inputs[3],45,67),(inputs[4],101,115),(inputs[6],30,56)]:
 b=p.read_bytes();ls=b.splitlines(keepends=True);end=min(end,len(ls));data=b''.join(ls[start-1:end]);dest=f'cuts/{p.stem}-{start}-{end}.lean';put(dest,data);cuts.append(dict(path=str(p),source=str(p),source_sha256=sha(b),start=start,end=end,inclusive=True,snapshot=dest,bytes=len(data),sha256=sha(data)))
draft=out/'SourceFlatPruningRecursiveCallbackResources.lean';s=draft.read_text();old=inputs[0].read_text()
def head(t):a=t.index('theorem callback_finite_complete_resources');return t[a:t.index(' := by',a)]
def normalize(t):
 for prefix in ['SourcePruningEnumerationRecursive.','SourceFlatPruningRecursive.']:t=t.replace(prefix,'')
 return re.sub(r'\s+','',t)
a=head(old);b=head(s);assert normalize(b).startswith(normalize(a));assert s.count('\n    callback_complete ')==1;assert 'canonical' not in s.lower()
put('contracts/original-head.txt',a.encode());put('contracts/proposed-head.txt',b.encode());js('contracts/retention.json',dict(retained_original_prefix=True,normalization='Whitespace and explicit old/new recursive namespace qualification only; the Complete input intentionally names the stronger flat induction contract',old_normalized_sha256=sha(normalize(a).encode()),producer_count_callback_complete=1,uniform_callback_bound_before_flat_input=True))
put('report.txt',b'''IMMUTABLE SOURCE-ONLY CALLBACK DRAFT. Public module SourceFlatPruningRecursiveCallbackResources; namespace SourceFlatPruningRecursive; theorem callback_finite_complete_resources. Root owns all builds and repository edits. The draft retains the full original callback certificate and actual old finite-hook resources, then appends actual flat execution and relation to the SAME old outcome.

The only changed input contract is the requested stronger smaller-depth Complete. Its universal original admission is unchanged. It retains the stable old run and old OutcomeResources and adds a flat replay family under a related current flat cache. That premise is intended to be discharged by outer depth induction. It is not a future successful callback or subtree premise.

The proof calls original callback_complete once before it quantifies any flat cache. It retains Packet, RenderStable, Frame, all metadata fields, every larger-fuel Success and exact old singleton, and the generic original continueWith execution equation. The callback producer therefore fixes one fuel/result/old core independently of the flat cache. Its true Boolean prunes and emits literal empty; no recursive invocation is needed. The proof derives actual flat singleton rows pointwise from that original success and reduces the actual flat continuation exactly.

For the false Boolean, Frame.values preserves the original mass ceiling. The new smaller-depth contract is invoked once at the returned original framed cache and full original Caller/Memos. Its work bound is also fixed before the universal flat cache. The sum of the callback and recursive bounds is used for both original and flat execution. At each larger common bound, successful replay supplies the actual flat callback core, full framed-cache relation and hence the IH input cache. The IH's actual flat run equation reduces to the resume call used by actual continueWith. Its ResultRelated compares against the SAME original outcome and all original OutcomeResources remain unchanged.

No Canonical, successful flat observation, desired returned cache, diagnostic exclusion, post-hook Ranges, native no-op subtree assumption or new producer premise is added. Native effects after an accepted callback belong to the actual recursive worker, not to the callback itself. The family permits a different existential flat endpoint at each larger bound. No global language or full-goal completion is asserted. The draft imports the exact contract proposal supplied by RequiredMemos; the copied input preserves its current source identity.
''')
js('source-pins.json',dict(version=1,status='IMMUTABLE SOURCE-ONLY PROPOSAL',sources=sources,cuts=cuts,draft=draft.name,draft_sha256=sha(draft.read_bytes()),contracts='contracts/retention.json',reviewer_builds=False))
for row in sources:assert Path(row['source']).read_bytes()==(out/row['snapshot']).read_bytes()
files=sorted(p for p in out.rglob('*') if p.is_file());payload=[dict(path=str(p.relative_to(out)),bytes=len(p.read_bytes()),sha256=sha(p.read_bytes())) for p in files];js('pins.json',dict(version=1,files=payload));js('FROZEN.json',dict(version=1,status='IMMUTABLE SOURCE-ONLY PROPOSAL',payload_count=len(payload),exact_file_count=len(payload)+2,pins_sha256=sha((out/'pins.json').read_bytes()),sources=len(sources),cuts=len(cuts),cut_lines=sum(r['end']-r['start']+1 for r in cuts),draft_sha256=sha(draft.read_bytes())))
for p in out.rglob('*'):
 if p.is_file():p.chmod(0o444)
print(json.dumps(dict(controls=json.loads((out/'FROZEN.json').read_text()),source_pins_sha256=sha((out/'source-pins.json').read_bytes()),report_sha256=sha((out/'report.txt').read_bytes()),frozen_sha256=sha((out/'FROZEN.json').read_bytes())),indent=2))
