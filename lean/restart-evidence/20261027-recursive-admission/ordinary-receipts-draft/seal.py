from pathlib import Path
import json,hashlib,datetime
out=Path('/tmp/mcfta-recursive-admission-20261027/ordinary-receipts-draft');sha=lambda b:hashlib.sha256(b).hexdigest()
assert not (out/'FROZEN.json').exists()
report=(out/'report.txt').read_text()
report=report.replace('SOURCE REVIEW CLEAR — OPEN PENDING ROOT CONSUMER REVIEW','FINAL SOURCE REVIEW CLEAR — PRODUCER AND ACTUAL SEMANTIC CONSUMERS',1)
report=report.replace('The bundle remains open because Root requested a hold for a separate producer semantic consumer review. No seal or publication is claimed by this report.','The subsequent actual semantic consumer review is included below. Root has now authorized this bundle seal. The seal records source/data review and Root\'s retained strict receipts; it makes no new publication or compiler-execution claim.')
report=report.replace('CONSUMER SOURCE REVIEW CLEAR; SEAL REMAINS HELD','FINAL CONSUMER SOURCE REVIEW CLEAR')
report=report.replace('The bundle is deliberately open until Root gives the final seal cue.','Root gave the final seal cue at 12:09 CET. The bundle now seals the exact reviewed checked sources.')
(out/'report.txt').write_text(report)
idx=json.loads((out/'source-pins.json').read_text());idx['status']='FINAL SOURCE REVIEW CLEAR; FROZEN'
for source in idx['sources']:
 b=Path(source['source']).read_bytes();assert b==(out/source['snapshot']).read_bytes() and sha(b)==source['sha256']
for c in idx['cuts']:
 b=b''.join(Path(c['source']).read_bytes().splitlines(keepends=True)[c['start']-1:c['end']]);assert b==(out/c['snapshot']).read_bytes() and sha(b)==c['sha256']
for e in idx.get('evidence',[]):
 b=Path(e['source']).read_bytes();assert b==(out/e['snapshot']).read_bytes() and sha(b)==e['sha256']
(out/'source-pins.json').write_text(json.dumps(idx,indent=2)+'\n')
status=json.loads((out/'review-status.json').read_text());status.update(status='FINAL SOURCE REVIEW CLEAR; FROZEN',reason='Root authorized seal at 2026-10-27 12:09 CET. Exact producer and actual semantic consumer sources/receipts retained.')
(out/'review-status.json').write_text(json.dumps(status,indent=2)+'\n')
files={}
for p in sorted(out.rglob('*')):
 if p.is_file() and p not in [out/'pins.json',out/'FROZEN.json']:
  b=p.read_bytes();files[str(p.relative_to(out))]=dict(bytes=len(b),sha256=sha(b))
now=datetime.datetime.now().astimezone().isoformat()
pins=dict(created=now,files=files);b=(json.dumps(pins,indent=2)+'\n').encode();(out/'pins.json').write_bytes(b)
frozen=dict(created=now,status='FROZEN / CLEAR',payload_count=len(files),exact_file_count=len(files)+2,pins_sha256=sha(b),pins_bytes=len(b),report_sha256=sha((out/'report.txt').read_bytes()),source_index_sha256=sha((out/'source-pins.json').read_bytes()),source_count=len(idx['sources']),cut_count=len(idx['cuts']),cut_lines=sum(c['end']-c['start']+1 for c in idx['cuts']),contract_comparison_sha256=sha((out/'contracts/comparison.json').read_bytes()),consumer_contract_comparison_sha256=sha((out/'consumer-review/comparison.json').read_bytes()),compiler_checks_executed_by_this_review=0)
(out/'FROZEN.json').write_text(json.dumps(frozen,indent=2)+'\n')
for name,pin in files.items():assert sha((out/name).read_bytes())==pin['sha256']
print(json.dumps(dict(**frozen,frozen_sha256=sha((out/'FROZEN.json').read_bytes())),indent=2))
