from pathlib import Path
import json,hashlib,re
repo=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA');area=Path('/tmp/mcfta-flat-recursive-20261027');out=area/'finite-head-draft';sha=lambda b:hashlib.sha256(b).hexdigest()
def put(rel,b):p=out/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
def js(rel,x):put(rel,(json.dumps(x,indent=2)+'\n').encode())
sources=[];cuts=[]
selection={
'SourcePruningEnumerationFiniteHeadResources':[(43,98),(134,163)],
'SourceFlatPruningNativeHeadResources':[(183,224)],
'SourceFlatPruningRecursiveReceiptResources':[(35,79)],
'SourceFlatPruningFiniteContract':[(30,56)],
'SourcePruningEnumerationSubtreeEffects':[(30,43)],
'SourcePruningEnumerationRecursiveReservation':[],
'SourcePruningEnumerationNativeBranchBoundedResources':[]}
for name,regions in selection.items():
 p=repo/f'{name}.lean';b=p.read_bytes();dest=f'inputs/{p.name}';put(dest,b);sources.append(dict(path=str(p),source=str(p),snapshot=dest,bytes=len(b),sha256=sha(b),read_scope='producer/header and relevant endpoint proof reviewed'))
 ls=b.splitlines(keepends=True)
 for start,end in regions:
  end=min(end,len(ls));assert start<=end;data=b''.join(ls[start-1:end]);dest=f'cuts/{name}-{start}-{end}.lean';put(dest,data);cuts.append(dict(path=str(p),source=str(p),source_sha256=sha(b),start=start,end=end,inclusive=True,snapshot=dest,bytes=len(data),sha256=sha(data)))
old=(repo/'SourcePruningEnumerationFiniteHeadResources.lean').read_text();draft=out/'SourceFlatPruningRecursiveHeadResources.lean';new=draft.read_text()
def header(t):a=t.index('theorem head_finite_complete_resources');return t[a:t.index(' := by',a)]
a=header(new);top=a.rindex(' ∧\n      (∀ (flat : FlatCached),');rest=a[:top];start=rest.index(' ∧\n          (∀ extra (flatReceipt : FlatReceipt');rest=rest[:start]+rest[rest.rindex(')'):];rest=rest.replace('          (match outcome with','          match outcome with').replace('          | .stopped _ _ _ => True))','          | .stopped _ _ _ => True)')
norm=lambda t:re.sub(r'\s+','',t);assert norm(rest)==norm(header(old))
put('contracts/original-head.txt',header(old).encode());put('contracts/proposed-head.txt',a.encode());js('contracts/projection.json',dict(entire_original_header_recovered=True,projection='Remove only outside flatHead family and inner flatHook family; remove the parentheses newly needed around the retained old match',normalized_old_sha256=sha(norm(header(old)).encode()),input_change='Complete intentionally resolves to new flat contract with same universal original admission',same_outcome_preserved=True))
put('report.txt',b'''IMMUTABLE SOURCE-ONLY HEAD DRAFT. SourceFlatPruningRecursiveHeadResources, namespace SourceFlatPruningNativeHookResources, theorem head_finite_complete_resources. Root owns all builds and repository changes. The original head contract is retained, with the requested stronger smaller-depth Complete. Two flat execution families are added at the same actual original witnesses.

The new NativeHeadResources.head_complete_cache_bounds producer runs once. Its complete original head Post, full middle Memos, Admitted/Pending/FragmentHistory, cache bounds and Fits/guard carrier are retained. Its actual flat head family is converted to a diagonal bound using the same original n/p/h ceilings. No cache or Caller endpoint is guessed or assumed. Unsupported projection retains the old unhandled branch and still supplies its actual flat head receipt.

A continuable original receipt invokes the new receipt_finite_complete_resources once. It produces the SAME old outcome, original actual callback family and OutcomeResources, plus the flat hook family. The common bound adds the head and callback bounds. Both actual flat head and actual flat hook families shift to that common work fuel. Noncomplete handled receipts emit literal empty outcomes; completed receipts execute the actual flat callback and its smaller-depth recursive worker. No future successful hook or flat observation is an input.

Inside the supported outcome packet, the entire old completed-captured-packet match is explicitly parenthesized. The flatHook family follows that whole match and refers to the same outcome. It is not scoped only under the stopped arm. The outside flatHead family is appended after the complete old head shape. Mechanical projection of only these two added families and the necessary match parentheses recovers the entire old declaration header modulo whitespace. Old resource fields, full Post/Memos, unchanged captured cache and rejection limits remain available. No Safe claim is made for rejection.

The immutable source inputs record current producer and contract versions. The two consumers may be checked and repaired in adopted repository copies by Root while this proposal remains unchanged. This local head lift does not itself establish the ordered sibling induction or the final arbitrary-depth flat theorem. No language acceptance or whole-goal completion is claimed.
''')
js('source-pins.json',dict(version=1,status='IMMUTABLE SOURCE-ONLY PROPOSAL',sources=sources,cuts=cuts,draft=draft.name,draft_sha256=sha(draft.read_bytes()),contract_projection='contracts/projection.json',reviewer_builds=False))
for row in sources:assert Path(row['source']).read_bytes()==(out/row['snapshot']).read_bytes()
files=sorted(p for p in out.rglob('*') if p.is_file());payload=[dict(path=str(p.relative_to(out)),bytes=len(p.read_bytes()),sha256=sha(p.read_bytes())) for p in files];js('pins.json',dict(version=1,files=payload));js('FROZEN.json',dict(version=1,status='IMMUTABLE SOURCE-ONLY PROPOSAL',payload_count=len(payload),exact_file_count=len(payload)+2,pins_sha256=sha((out/'pins.json').read_bytes()),sources=len(sources),cuts=len(cuts),cut_lines=sum(r['end']-r['start']+1 for r in cuts),draft_sha256=sha(draft.read_bytes())))
for p in out.rglob('*'):
 if p.is_file():p.chmod(0o444)
print(json.dumps(dict(controls=json.loads((out/'FROZEN.json').read_text()),source_pins_sha256=sha((out/'source-pins.json').read_bytes()),report_sha256=sha((out/'report.txt').read_bytes()),frozen_sha256=sha((out/'FROZEN.json').read_bytes())),indent=2))
