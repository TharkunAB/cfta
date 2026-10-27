from pathlib import Path
import hashlib,json,datetime,difflib
repo=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-recursive-history-resources-20261027');out=area/'head-history-draft';sha=lambda b:hashlib.sha256(b).hexdigest();assert not (out/'FROZEN.json').exists()
module='SourcePruningEnumerationFiniteHeadHistory';p=repo/'lean/MicroCFTA'/(module+'.lean');raw=p.read_bytes();expected='1a637da6db18594cea769bbcc9642e08060feb47770e09dda69894886e6a61e1';assert sha(raw)==expected
q=out/'checked-source'/p.name;q.parent.mkdir(exist_ok=True);q.write_bytes(raw)
idx=json.loads((out/'source-pins.json').read_text());idx.setdefault('evidence',[]);history=[];revision_names=['001-initial.lean','002-root-record-layout.lean','003-root-strict-clean.lean']
for number,revision in enumerate(revision_names,1):
 name=f'strict-head-history-{number}';r=json.loads((area/name/'report.json').read_text());source=(area/name/'MicroCFTA'/p.name).read_bytes();assert sha(source)==r['source_sha256']
 q=out/'revisions'/revision
 if q.exists():assert q.read_bytes()==source
 else:q.write_bytes(source)
 dest=out/'evidence'/name;(dest/'MicroCFTA').mkdir(parents=True,exist_ok=True)
 for rel in ['report.json','raw.log','MicroCFTA/'+p.name]:
  original=area/name/rel;b=original.read_bytes();(dest/rel).write_bytes(b);idx['evidence'].append(dict(source=str(original),snapshot=str((dest/rel).relative_to(out)),bytes=len(b),sha256=sha(b)))
 history.append(dict(revision=revision,source_sha256=sha(source),strict=name,exit_code=r['exit_code'],raw_bytes=r['bytes'],raw_sha256=r['sha256']))
assert history[-1]['exit_code']==0 and (out/'evidence/strict-head-history-3/raw.log').read_bytes()==b''
for a,b in zip(revision_names,revision_names[1:]):
 sa=(out/'revisions'/a).read_text();sb=(out/'revisions'/b).read_text()
 for before,after,x,y in [(a,b,sa,sb),(b,a,sb,sa)]:
  (out/'revisions'/(before[:3]+'-to-'+after[:3]+'.patch')).write_text(''.join(difflib.unified_diff(x.splitlines(keepends=True),y.splitlines(keepends=True),fromfile=before,tofile=after)))
(out/'revisions/history.json').write_text(json.dumps(history,indent=2)+'\n')
# Compare the exact old declaration after dropping only the new supported history packet.
oldtext=(repo/'lean/MicroCFTA/SourcePruningEnumerationCallbackAdmission.lean').read_text()
def header(s,name):
 s=s[s.index('theorem '+name):];return s[:s.index(' := by')]
old=header(oldtext,'head_finite_complete_resources_with_callback_admission');append=(out/'supported-history-appendix.txt').read_text();comparisons=[]
for revision in revision_names:
 s=(out/'revisions'/revision).read_text();new=header(s,'head_finite_complete_resources_with_history');actualAppend=append
 if '| .complete fragment actual _queries after =>' in new:actualAppend=append.replace('| .complete fragment actual queries after =>','| .complete fragment actual _queries after =>',1)
 restored=new.replace(actualAppend,'          | .stopped _ _ _ => True) ∧',1).replace('          (match outcome with','          match outcome with',1).replace('head_finite_complete_resources_with_history','head_finite_complete_resources_with_callback_admission',1).replace('(recursive : CompleteWithHistory (bits := bits)','(recursive : Complete (bits := bits)',1)
 assert restored==old,revision
 comparisons.append(dict(revision=revision,entire_old_contract_literal_after_precise_restoration=True,restored_sha256=sha(restored.encode())))
(out/'contracts/final-entire-contract.txt').write_text(header(raw.decode(),'head_finite_complete_resources_with_history'));(out/'contracts/final-restored-old-contract.txt').write_text(old)
comp=json.loads((out/'contracts/comparison.json').read_text());comp.update(all_revisions=comparisons,final_source_sha256=expected,root_strict3_pass=True,changed_new_match_binder='unused queries renamed _queries only',original_contract_restored_byte_identically=True)
(out/'contracts/comparison.json').write_text(json.dumps(comp,indent=2)+'\n')
snapshot='inputs/lean/MicroCFTA/'+p.name;(out/snapshot).write_bytes(raw);idx['sources'].append(dict(path=str(p),source=str(p),snapshot=snapshot,bytes=len(raw),sha256=expected,read_scope='whole final checked head-history source reviewed; exact two Root corrections compared against original draft'))
text=raw.decode();startpos=text.index('theorem head_finite_complete_resources_with_history');endpos=text.index(' := by',startpos)+len(' := by');start=text[:startpos].count('\n')+1;end=text[:endpos].count('\n')+1;b=b''.join(raw.splitlines(keepends=True)[start-1:end]);snapshot=f'cuts/{module}--{start}-{end}.lean';(out/snapshot).write_bytes(b);idx['cuts'].append(dict(path=str(p),source=str(p),snapshot=snapshot,start=start,end=end,source_sha256=expected,bytes=len(b),sha256=sha(b)))
report=(out/'report.txt').read_text();(out/'revisions/initial-report.txt').write_text(report)
report=report.replace('REAL HEAD-HISTORY COMPOSITION DRAFT COMPLETE; ROOT STRICT CHECK PENDING','FINAL REAL HEAD-HISTORY SOURCE REVIEW CLEAR').replace('The bundle stays open for Root\'s actual strict snapshots.','Root supplied all three actual strict snapshots and authorized the final seal. They are now retained.')
report+='''\nFinal source and strict review: Root changed only the final record-update layout and the unused queries pattern in the appended packet to _queries. Strict1 retains its layout parse failure and exact source. Strict2 retains only the unused pattern lint failure and exact source. Strict3 passes with warnings as errors/all linters and literal empty output at final SHA256 1a637da6db18594cea769bbcc9642e08060feb47770e09dda69894886e6a61e1. The repository source, checked-source copy and strict3 input are byte-identical. All three revisions restore the same complete 5418-byte original head declaration, SHA256 dde15c668533e8b8da1029bacdeb6542d7eae8cea5318c5db538e9e8fa6d5197, after precisely removing the new appendix, reversing the theorem name and forgetting the explicit stronger smaller-depth hypothesis. No public original premise or old output field was dropped.\n\nThe final corrected source was reviewed against the complete draft and exact directional deltas. The old and rich actual callback outcomes are aligned by equality at the common adequate work fuel. The proof does not equate any old/new full memo witnesses from their query projections. The rebase affects only stable running fields; native Post, input/returned full Memos, Packet, resource bounds and captured endpoint remain the original witnesses. Generic callback observations still handle both callback flags; the false-only ResourceHistory family does not become a success assumption. No new runtime or datatype exists in this module. This worker executes no check and changes no repository or prior sealed bundle. The source-claim scope is this real local head composition, conditional on the explicit smaller-depth CompleteWithHistory induction hypothesis; positive current-depth closure remains separate.\n'''
(out/'report.txt').write_text(report);idx['status']='FINAL SOURCE REVIEW CLEAR; FROZEN';(out/'source-pins.json').write_text(json.dumps(idx,indent=2)+'\n')
for s in idx['sources']:
 b=Path(s['source']).read_bytes();assert b==(out/s['snapshot']).read_bytes() and sha(b)==s['sha256']
for c in idx['cuts']:
 b=b''.join(Path(c['source']).read_bytes().splitlines(keepends=True)[c['start']-1:c['end']]);assert b==(out/c['snapshot']).read_bytes() and sha(b)==c['sha256']
for e in idx['evidence']:
 b=Path(e['source']).read_bytes();assert b==(out/e['snapshot']).read_bytes() and sha(b)==e['sha256']
now=datetime.datetime.now().astimezone().isoformat();files={}
for q in sorted(out.rglob('*')):
 if q.is_file() and q not in [out/'pins.json',out/'FROZEN.json']:
  b=q.read_bytes();files[str(q.relative_to(out))]=dict(bytes=len(b),sha256=sha(b))
b=(json.dumps(dict(created=now,files=files),indent=2)+'\n').encode();(out/'pins.json').write_bytes(b)
frozen=dict(created=now,status='FROZEN / CLEAR',payload_count=len(files),exact_file_count=len(files)+2,pins_sha256=sha(b),pins_bytes=len(b),report_sha256=sha((out/'report.txt').read_bytes()),source_index_sha256=sha((out/'source-pins.json').read_bytes()),source_count=len(idx['sources']),cut_count=len(idx['cuts']),cut_lines=sum(c['end']-c['start']+1 for c in idx['cuts']),contract_comparison_sha256=sha((out/'contracts/comparison.json').read_bytes()),final_source_sha256=expected,compiler_checks_executed_by_this_review=0)
(out/'FROZEN.json').write_text(json.dumps(frozen,indent=2)+'\n')
for name,pin in files.items():assert sha((out/name).read_bytes())==pin['sha256']
print(json.dumps(dict(**frozen,frozen_sha256=sha((out/'FROZEN.json').read_bytes())),indent=2))
