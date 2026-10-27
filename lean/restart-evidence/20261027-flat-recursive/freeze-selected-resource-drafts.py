from pathlib import Path
import json,hashlib,re
repo=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA');out=Path('/tmp/mcfta-flat-recursive-20261027/selected-resources-draft');sha=lambda b:hashlib.sha256(b).hexdigest()
def put(rel,b):p=out/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
def js(rel,x):put(rel,(json.dumps(x,indent=2)+'\n').encode())
sources=[];cuts=[]
for name in ['SourceFlatPruningSelectedCompletion','SourcePruningEnumerationSelectedEdgeResources','SourceFlatPruningTraversalResources','SourceFlatPruningCapturedCompletion','SourcePruningEnumerationCapturedEdgeResources','SourceFlatPruningCapturedEdge','SourceFlatPruningOwnObservation']:
 p=repo/f'{name}.lean';b=p.read_bytes();dest=f'inputs/{p.name}';put(dest,b);sources.append(dict(path=str(p),source=str(p),snapshot=dest,bytes=len(b),sha256=sha(b)))
for name,token in [('SourcePruningEnumerationSelectedEdgeResources','complete_with_fragments_resources'),('SourcePruningEnumerationCapturedEdgeResources','complete_with_history_resources'),('SourceFlatPruningTraversalResources','complete_with_fragments_resources'),('SourceFlatPruningCapturedEdge','run_completed')]:
 p=repo/f'{name}.lean';b=p.read_bytes();lines=b.splitlines(keepends=True);start=next(i for i,x in enumerate(lines) if x.startswith(('theorem '+token).encode()));end=start
 while b':= by' not in lines[end]:end+=1
 data=b''.join(lines[start:end+1]);dest=f'cuts/{name}-{start+1}-{end+1}.lean';put(dest,data);cuts.append(dict(path=str(p),source=str(p),source_sha256=sha(b),start=start+1,end=end+1,inclusive=True,snapshot=dest,bytes=len(data),sha256=sha(data)))
def head(t,token):a=t.index('theorem '+token);return t[a:t.index(' := by',a)]
contracts=[]
for new,old,token in [('SourceFlatPruningSelectedResources','SourcePruningEnumerationSelectedEdgeResources','complete_with_fragments_resources'),('SourceFlatPruningCapturedResources','SourcePruningEnumerationCapturedEdgeResources','complete_with_history_resources')]:
 n=head((out/f'{new}.lean').read_text(),token);o=head((repo/f'{old}.lean').read_text(),token);norm=lambda s:re.sub(r'\s+','',s);assert norm(n).startswith(norm(o));contracts.append(dict(new=new,old=old,theorem=token,old_header_sha256=sha(o.encode()),normalized_old_sha256=sha(norm(o).encode()),entire_old_header_is_prefix=True,normalization='whitespace only',old_packet_flattened=True))
js('contracts.json',contracts)
put('report.txt',b'''SOURCE-ONLY DRAFTS. Root owns all Lean checks and repository changes. These immutable proposals have not been compiled by this reviewer. They preserve the entire old resource theorem headers and flattened conclusions. A whitespace-only comparison verifies that each exact old declaration type is the prefix before the appended flat family. No old Ranges input remains.

SelectedResources.complete_with_fragments_resources consumes the actual EdgeInputs own-prefix once and the coupled TraversalResources producer once. The same traversal witnesses supply the full original Post, Memos, histories, root protection, native Fits and guard carrier. The original resource count remains SelectedEdge.cost edge scs before.core.counter tries. Actual own preparation replays to the flat staged values/buckets. The residual update is applied only after completed children. Both completion and actual raw-empty stopping preserve the resource fields before the appended flat relation.

CapturedResources.complete_with_history_resources retains the original resource producer once, and obtains the coupled selected resource family under the same current premises. Common representative/native/index sums and p/h maxima align actual old execution. No equality between independently produced caches is assumed. The literal old captured run identifies the retained final result. Pure run_completed transports the actual selected execution through finalization. The same final old storage/roots/counts/flags and full cache relation derive conditional native Correct for complete and valid stopped candidates; other shapes are excluded by the retained old shape. No Safe is asserted on rejection. The complete old resource packet is flattened before that final flat family, as requested.

No producer is rerun at runtime by either proof. No future flat observation, final desired cache, semantic gate, post-hook Ranges or new original admission premise is added. Per-run flat endpoints remain existential after uniform native bounds. These two local lifts do not establish whole recursive correspondence, language soundness or coverage. The seven source snapshots record exact inputs used for the drafts, including Root's current TraversalResources proposal. Root may apply elaboration fixes to adopted copies while these proposal bytes remain unchanged.
''')
js('source-pins.json',dict(version=1,status='IMMUTABLE SOURCE-ONLY PROPOSALS',sources=sources,cuts=cuts,contracts='contracts.json',compiled_by_reviewer=False))
for row in sources:assert Path(row['source']).read_bytes()==(out/row['snapshot']).read_bytes()
files=sorted(p for p in out.rglob('*') if p.is_file());payload=[dict(path=str(p.relative_to(out)),bytes=len(p.read_bytes()),sha256=sha(p.read_bytes())) for p in files];js('pins.json',dict(version=1,files=payload));js('FROZEN.json',dict(version=1,status='IMMUTABLE SOURCE-ONLY PROPOSALS',payload_count=len(payload),exact_file_count=len(payload)+2,pins_sha256=sha((out/'pins.json').read_bytes()),sources=len(sources),cuts=len(cuts),cut_lines=sum(x['end']-x['start']+1 for x in cuts)))
for p in out.rglob('*'):
 if p.is_file():p.chmod(0o444)
print(json.dumps(dict(controls=json.loads((out/'FROZEN.json').read_text()),report_sha256=sha((out/'report.txt').read_bytes()),source_pins_sha256=sha((out/'source-pins.json').read_bytes()),frozen_sha256=sha((out/'FROZEN.json').read_bytes())),indent=2))
