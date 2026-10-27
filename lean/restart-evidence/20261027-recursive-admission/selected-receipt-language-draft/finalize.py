from pathlib import Path
import hashlib,json,datetime,difflib
repo=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-recursive-admission-20261027');out=area/'selected-receipt-language-draft';sha=lambda b:hashlib.sha256(b).hexdigest()
assert not (out/'FROZEN.json').exists()
module='SourcePruningEnumerationSelectedReceiptLanguage';p=repo/'lean/MicroCFTA'/(module+'.lean');raw=p.read_bytes();expected='dcbe0f6d62c5793053594e0679a51e37c984323d0cfe5f1d9b01b3d0d88fec6d';assert sha(raw)==expected
q=out/'checked-source'/p.name;q.parent.mkdir(exist_ok=True);q.write_bytes(raw)
idx=json.loads((out/'source-pins.json').read_text());evidence=idx.get('evidence',[]);seen={e['snapshot'] for e in evidence}
revision_names=['001-initial.lean','002-actual-entry-values.lean','003-root-namespace.lean','004-root-strict-clean.lean'];history=[]
for number,revision in enumerate(revision_names,1):
 name=f'strict-selected-receipt-language-{number}';dest=out/'evidence'/name;(dest/'MicroCFTA').mkdir(parents=True,exist_ok=True)
 report=json.loads((area/name/'report.json').read_text());source=(area/name/'MicroCFTA'/p.name).read_bytes();assert sha(source)==report['source_sha256']
 target=out/'revisions'/revision
 if target.exists():assert target.read_bytes()==source
 else:target.write_bytes(source)
 for rel in ['report.json','raw.log','MicroCFTA/'+p.name]:
  original=area/name/rel;b=original.read_bytes();destfile=dest/rel;destfile.write_bytes(b);snapshot=str(destfile.relative_to(out))
  if snapshot not in seen:evidence.append(dict(source=str(original),snapshot=snapshot,bytes=len(b),sha256=sha(b)));seen.add(snapshot)
 history.append(dict(revision=revision,source_sha256=sha(source),strict=name,exit_code=report['exit_code'],output_bytes=report['bytes'],output_sha256=report['sha256']))
assert history[-1]['exit_code']==0 and (out/'evidence/strict-selected-receipt-language-4/raw.log').read_bytes()==b''
for prev,following in zip(revision_names,revision_names[1:]):
 a=(out/'revisions'/prev).read_text();b=(out/'revisions'/following).read_text();stem=prev[:3]+'-to-'+following[:3]
 (out/'revisions'/(stem+'.patch')).write_text(''.join(difflib.unified_diff(a.splitlines(keepends=True),b.splitlines(keepends=True),fromfile=prev,tofile=following)))
 (out/'revisions'/(following[:3]+'-to-'+prev[:3]+'.patch')).write_text(''.join(difflib.unified_diff(b.splitlines(keepends=True),a.splitlines(keepends=True),fromfile=following,tofile=prev)))
(out/'revisions/history.json').write_text(json.dumps(history,indent=2)+'\n')
initial=(out/'revisions/001-initial.lean').read_text();final=raw.decode()
def header(s):
 s=s[s.index('theorem narrowed_receipt_sound'):];return s[:s.index(' := by')]
assert header(initial)==header(final)
(out/'contracts/final-public-contract.txt').write_text(header(final));comparison=json.loads((out/'contracts/comparison.json').read_text());comparison.update(all_four_revisions_public_contract_byte_identical=all(header((out/'revisions'/r).read_text())==header(initial) for r in revision_names),final_source_sha256=expected,root_strict4_pass=True,new_runtime_definitions=0,new_producer_calls=0)
(out/'contracts/comparison.json').write_text(json.dumps(comparison,indent=2)+'\n')
snapshot='inputs/lean/MicroCFTA/'+p.name;(out/snapshot).write_bytes(raw);idx['sources'].append(dict(path=str(p),source=str(p),snapshot=snapshot,bytes=len(raw),sha256=expected,read_scope='whole final actual checked module source reviewed; same original public contract across all revisions'))
lines=raw.splitlines(keepends=True)
spans=[]
start=final.index('private theorem entry_values');end=final.index('\nvariable [DecidableEq Symbol]',start);spans.append((final[:start].count('\n')+1,final[:end].count('\n')))
start=final.index('theorem narrowed_receipt_sound');end=final.index(' := by',start)+len(' := by');spans.append((final[:start].count('\n')+1,final[:end].count('\n')+1))
for start,end in spans:
 b=b''.join(lines[start-1:end]);snapshot=f'cuts/{module}--{start}-{end}.lean';(out/snapshot).write_bytes(b);idx['cuts'].append(dict(path=str(p),source=str(p),snapshot=snapshot,start=start,end=end,source_sha256=expected,bytes=len(b),sha256=sha(b)))
idx['evidence']=evidence;idx['status']='FINAL SOURCE CLAIM REVIEW CLEAR; FROZEN';idx['final_source_sha256']=expected
(out/'source-pins.json').write_text(json.dumps(idx,indent=2)+'\n')
(out/'revisions/report-before-final.txt').write_bytes((out/'report.txt').read_bytes())
report=(out/'report.txt').read_text().replace('SOURCE-CONNECTED REVISION002 COMPLETE; ROOT CHECK PENDING','FINAL SOURCE CLAIM REVIEW CLEAR').replace('The new bundle remains open for Root\'s strict feedback and exact checked source capture.','The exact final installed source and all four strict attempts are now retained. Root authorized this final source review and seal.')
report+='''\nFinal checked-source review: Root added EnumerationSchedule to resolve reject_unsuccessful, then moved the public theorem's three DecidableEq section variables below the independent private entry observer. No input or conclusion changed. All four public declaration texts are byte-identical, SHA256 d6c6fd1d355254187c2771806e292f01bf5fc58cacc6c0461d14d725a6440c08. Strict1 retains the dependent-match failure. Strict2 retains three unresolved reject_unsuccessful names. Strict3 retains only unused private theorem instance arguments. Strict4 passes all linters with warnings as errors and a literal empty log at final source dcbe0f6d62c5793053594e0679a51e37c984323d0cfe5f1d9b01b3d0d88fec6d. The source is identical to Root's installed repository file and immutable strict4 input.\n\nThe final proof was read in full. The private entry observer uses actual successful getValue and representative frames, then the actual ancestry-only modify. It proves exact stored-values equality. The public proof derives a literal narrowed PrefixValid copy before invoking the dependent cache observer. It derives Canonical, Safe/cache/pending/order, the original chosen Ready and actual PendingRealized; it constructs the same native/full-memo narrowed Packet and composes the existing actual ordinary false-callback law with PrefixMeaning. The stored-slot witness is restored to the original narrowed core through the exact actual entry equality. No native Caller, input/output heap or full memo endpoint is identified from a query projection.\n\nThis is one conditional actual selected-step backward law, not a whole recursive semantic theorem or a producer guarantee of successful callbacks. The actual observation premises describe the already reached prefix, entry, head and false callback. The only satisfaction premise belongs to the actual callback endpoint inside the implication. Initial Canonical and the nonterminal/fresh-arity/retention gates remain explicit. The global H6 scope is unchanged. This review changes no repository source, runs no Lean/build/native/Git/network operation, and leaves earlier frozen bundles unchanged.\n'''
(out/'report.txt').write_text(report)
for s in idx['sources']:
 b=Path(s['source']).read_bytes();assert b==(out/s['snapshot']).read_bytes() and sha(b)==s['sha256']
for c in idx['cuts']:
 b=b''.join(Path(c['source']).read_bytes().splitlines(keepends=True)[c['start']-1:c['end']]);assert b==(out/c['snapshot']).read_bytes() and sha(b)==c['sha256']
for e in evidence:
 b=Path(e['source']).read_bytes();assert b==(out/e['snapshot']).read_bytes() and sha(b)==e['sha256']
now=datetime.datetime.now().astimezone().isoformat();files={}
for p in sorted(out.rglob('*')):
 if p.is_file() and p not in [out/'pins.json',out/'FROZEN.json']:
  b=p.read_bytes();files[str(p.relative_to(out))]=dict(bytes=len(b),sha256=sha(b))
pins=dict(created=now,files=files);b=(json.dumps(pins,indent=2)+'\n').encode();(out/'pins.json').write_bytes(b)
frozen=dict(created=now,status='FROZEN / CLEAR',payload_count=len(files),exact_file_count=len(files)+2,pins_sha256=sha(b),pins_bytes=len(b),report_sha256=sha((out/'report.txt').read_bytes()),source_index_sha256=sha((out/'source-pins.json').read_bytes()),source_count=len(idx['sources']),cut_count=len(idx['cuts']),cut_lines=sum(c['end']-c['start']+1 for c in idx['cuts']),contract_comparison_sha256=sha((out/'contracts/comparison.json').read_bytes()),final_source_sha256=expected,compiler_checks_executed_by_this_review=0)
(out/'FROZEN.json').write_text(json.dumps(frozen,indent=2)+'\n')
assert len([p for p in out.rglob('*') if p.is_file()])==len(files)+2
for name,pin in files.items():assert sha((out/name).read_bytes())==pin['sha256']
print(json.dumps(dict(**frozen,frozen_sha256=sha((out/'FROZEN.json').read_bytes())),indent=2))
