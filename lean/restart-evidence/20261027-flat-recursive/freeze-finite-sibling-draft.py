from pathlib import Path
import json,re,hashlib
repo=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA');out=Path('/tmp/mcfta-flat-recursive-20261027/finite-sibling-draft');sha=lambda b:hashlib.sha256(b).hexdigest()
def put(rel,b):p=out/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
def js(rel,x):put(rel,(json.dumps(x,indent=2)+'\n').encode())
names=['SourcePruningEnumerationFiniteSiblingResources','SourcePruningEnumerationFiniteSiblingFinishResources','SourceFlatPruningRecursiveHeadResources','SourceFlatPruningContinuationHead','SourceFlatPruningRecursiveBase','SourceFlatPruningFiniteContract','SourceFlatPruningNativeContinuations','SourceFlatPruningNativeBranches','SourceFlatPruningRecursive']
sources=[];cuts=[]
for name in names:
 p=repo/f'{name}.lean';b=p.read_bytes();dest=f'inputs/{name}.lean';put(dest,b);sources.append(dict(path=str(p),source=str(p),snapshot=dest,bytes=len(b),sha256=sha(b),read_scope='actual API and endpoint composition reviewed'))
for name,token in [('SourcePruningEnumerationFiniteSiblingResources','alternatives_finite_complete_resources'),('SourcePruningEnumerationFiniteSiblingFinishResources','alternatives_finite_finish_resources'),('SourceFlatPruningRecursiveHeadResources','head_finite_complete_resources'),('SourceFlatPruningContinuationHead','continued_head'),('SourceFlatPruningRecursiveBase','advance_related'),('SourceFlatPruningRecursiveBase','finish_related')]:
 p=repo/f'{name}.lean';b=p.read_bytes();ls=b.splitlines(keepends=True);start=next(i for i,l in enumerate(ls) if l.startswith(('theorem '+token).encode()));end=start
 while b':= by' not in ls[end]:end+=1
 data=b''.join(ls[start:end+1]);dest=f'cuts/{name}-{start+1}-{end+1}.lean';put(dest,data);cuts.append(dict(path=str(p),source=str(p),source_sha256=sha(b),start=start+1,end=end+1,inclusive=True,snapshot=dest,bytes=len(data),sha256=sha(data),meaning=token+' exact header'))
draft=out/'SourceFlatPruningRecursiveSiblingResources.lean';text=draft.read_text();contracts=[]
def head(t,token):a=t.index('theorem '+token);return t[a:t.index(' := by',a)]
def norm(s):return re.sub(r'\s+','',s.replace('SourcePruningEnumerationRecursive.Complete','SourceFlatPruningRecursive.Complete'))
for oldName,token in [('SourcePruningEnumerationFiniteSiblingResources','alternatives_finite_complete_resources'),('SourcePruningEnumerationFiniteSiblingFinishResources','alternatives_finite_finish_resources')]:
 a=head((repo/f'{oldName}.lean').read_text(),token);b=head(text,token);assert norm(b).startswith(norm(a));put(f'contracts/{token}-old.txt',a.encode());contracts.append(dict(theorem=token,entire_original_header_is_prefix=True,old_normalized_sha256=sha(norm(a).encode()),normalization='Whitespace only, plus intentional stronger Complete namespace',old_packet_flattened=True,flat_family_last=True))
js('contracts/retention.json',contracts)
put('report.txt',b'''IMMUTABLE SOURCE-ONLY SIBLING PROPOSAL. Module SourceFlatPruningRecursiveSiblingResources, namespace SourceFlatPruningNativeFiniteSiblingResources. The draft includes alternatives_finite_complete_resources and alternatives_finite_finish_resources. Root owns all repository changes and builds. Both headers retain the entire old inputs and flattened conclusions, except for the requested stronger smaller-depth Complete. Each appends its actual flat scan family LAST. The finished theorem keeps the complete old OutcomeResources before that family.

The induction uses the new coupled RecursiveHeadResources producer once per reached head. The actual head and same-outcome hook families run at the common work bound. A completed hook supplies its actual returned Caller, query and full Memos. These enter the suffix under the corresponding Post.context and captured Packet. Every sibling restores the same captured enumeration cache and metadata. It does not restore the native caller. The tail uses the actual callback/subtree endpoint and the next planned reservation seed. There is no post-hook Ranges premise.

A private continued_hook lemma reads the actual flat hook relation. For a completed receipt it identifies the actual flat outputs and literal hook Caller/query. For handled noncomplete receipts it uses advance_related and the empty-output relation. continued_head then composes that exact head with the actual flat suffix. OrderedRelated append preserves all output positions and duplicates. Receipts retain ordered correspondence. The old ReceiptAt/OutputAt/StoppedAt certificates, full Post and Memos, mass ceilings, Fits/carriers, length bounds and exact shape remain unchanged.

A stopped hook retains all emitted outputs, its related nested reason and the exact optional endpoint. The current receipt remains outside the processed prefix. Earlier output prefixes are retained when a suffix stops. An unsupported head retains the actual unhandled receipt and does not execute a hook or suffix. No endpoint is supplied when the actual result omits it. Rejection does not acquire a Safe assertion.

The finish wrapper calls the new full scan producer once. It preserves every old witness and certificate, derives the original finished OutcomeResources from those same witnesses, and carries the flat scan family unchanged. Existing finish_related converts that family to the actual recursive finished result. No independent producer result is aligned by an assumed cache equality.

Bounds precede the universal related flat input. Each larger bound obtains its actual flat fold existentially. No future successful hook, desired final cache, flat observation or final invariant is an original premise. Depth induction must discharge the stronger Complete argument. This module alone does not assert the final arbitrary-depth theorem or language acceptance/coverage. The pre-scope-review proposal is retained unchanged as provenance; the final proposal moves private helpers before section instances and uses explicit endpoint substitutions. No compiler was run by this reviewer.
''')
js('source-pins.json',dict(version=1,status='IMMUTABLE SOURCE-ONLY PROPOSAL',sources=sources,cuts=cuts,draft=draft.name,draft_sha256=sha(draft.read_bytes()),contracts='contracts/retention.json',reviewer_builds=False))
for row in sources:assert Path(row['source']).read_bytes()==(out/row['snapshot']).read_bytes()
files=sorted(p for p in out.rglob('*') if p.is_file());payload=[dict(path=str(p.relative_to(out)),bytes=len(p.read_bytes()),sha256=sha(p.read_bytes())) for p in files];js('pins.json',dict(version=1,files=payload));js('FROZEN.json',dict(version=1,status='IMMUTABLE SOURCE-ONLY PROPOSAL',payload_count=len(payload),exact_file_count=len(payload)+2,pins_sha256=sha((out/'pins.json').read_bytes()),sources=len(sources),cuts=len(cuts),cut_lines=sum(r['end']-r['start']+1 for r in cuts),draft_sha256=sha(draft.read_bytes())))
for p in out.rglob('*'):
 if p.is_file():p.chmod(0o444)
print(json.dumps(dict(controls=json.loads((out/'FROZEN.json').read_text()),report_sha256=sha((out/'report.txt').read_bytes()),source_pins_sha256=sha((out/'source-pins.json').read_bytes()),frozen_sha256=sha((out/'FROZEN.json').read_bytes())),indent=2))
