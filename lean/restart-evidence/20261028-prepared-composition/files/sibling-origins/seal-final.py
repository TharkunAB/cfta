from pathlib import Path
import hashlib,json,datetime,re
p=Path('/tmp/mcfta-prepared-composition-20261028/sibling-origins')
def sha(b):return hashlib.sha256(b).hexdigest()
def check_pin(pin):
    b=(p/pin['path']).read_bytes();assert len(b)==pin['bytes'] and sha(b)==pin['sha256'],pin['path'];return b
assert not (p/'pins.json').exists() and not (p/'FROZEN.json').exists()
assert not any(x.is_symlink() for x in p.rglob('*'))
idx=json.loads((p/'source-index.json').read_text());cuts=0
for r in idx['sources']:
    b=check_pin(r['whole']);assert Path(r['source']).read_bytes()==b,r['source'];lines=b.splitlines(keepends=True)
    for c in r['cuts']:
        cb=check_pin(c);assert cb==b''.join(lines[c['first_line']-1:c['last_line']]);cuts+=1
for a,b in [('complete-admission-resource-prefix-original.lean','complete-admission-resource-prefix-recovered.lean'),('entire-sibling-result-original.lean','entire-sibling-result-parent-recovered.lean'),('entire-original-receipt-model-declaration.lean','entire-receipt-model-declaration-recovered.lean')]:
    assert (p/'cuts'/a).read_bytes()==(p/'cuts'/b).read_bytes()
docs=json.loads((p/'document-inverse-review-final.json').read_text());check_pin(docs['whole_new_note'])
for d in docs['insertions']:
    prior=check_pin(d['prior']);ins=check_pin(d['insert']);a=d['insertion_first_byte'];current=prior[:a]+ins+prior[a:]
    assert len(current)==d['current_bytes'] and sha(current)==d['current_sha256'];assert Path(d['source']).read_bytes()==current
    assert current[:a]+current[a+len(ins):]==prior
scope=json.loads((p/'public-read-scopes-v1.json').read_text());raw=(p/'integration/public-readback-final/raw.log').read_bytes();prior=(p/'integration/prior-public-readback/raw.log').read_bytes();assert raw.startswith(prior)
assert len(raw)==scope['raw_bytes'] and sha(raw)==scope['raw_sha256'];assert raw[len(prior):]==(p/'integration/new-public-blocks.txt').read_bytes()
for b in scope['blocks']:
    block=check_pin(b);assert raw[b['raw_first_byte']:b['raw_last_byte_exclusive']]==block;assert b'Quot.sound]' in block and b'Classical.choice' in block and b'propext' in block
    assert b'\xe2\x80\xa6' not in block
commands=json.loads((p/'command-index-final.json').read_text())
for c in commands['commands']:
    d=p/c['copy'];r=json.loads((d/'report.json').read_text());b=(d/'raw.log').read_bytes();assert len(b)==c['bytes']==r['bytes'] and sha(b)==c['sha256']==r['sha256'];assert r['exit_code']==c['exit_code']
    limits=r['cgroup_limits'];assert limits['memory.max']==limits['memory.high']=='4294967296' and limits['memory.swap.max']=='0'
assert commands['current_commands']==17 and commands['inherited_commands']==1 and commands['current_failed_compiler_commands']==5
for folder,name in [('sibling-v1','SourcePruningEnumerationPreparedFiniteSiblingOrigins.lean'),('parent-v2','SourcePruningEnumerationPreparedFiniteParentOrigins.lean'),('receipt-v1','SourcePruningEnumerationPreparedFiniteReceiptOrigins.lean')]:
    d=p/'checks'/folder;assert (d/'raw.log').read_bytes()==b'';assert (d/'MicroCFTA'/name).read_bytes()==(p/'sources'/name).read_bytes()
    text=(p/'sources'/name).read_text();assert not re.search(r'\b(sorry|axiom|native_decide)\b',text)
ver={'status':'PASS','source_wholes':len(idx['sources']),'literal_source_cuts':cuts,'exact_contract_recovery_pairs':3,'whole_assigned_public_blocks':3,'whole_assigned_public_bytes':scope['whole_assigned_bytes'],'whole_assigned_public_lines':scope['whole_assigned_lines'],'document_inverse_records':len(docs['insertions']),'current_commands':17,'inherited_commands':1,'current_failed_compiler_commands':5,'owner_compiler_commands':0,'all_current_source_wholes_match_live':True,'old_document_whole_semantic_review_claimed':False,'write_halt_after_seal':True}
(p/'verification-final.json').write_text(json.dumps(ver,indent=2)+'\n')
payloads=[]
for f in sorted(p.rglob('*')):
    if f.is_file() and f.name not in ['pins.json','FROZEN.json']:
        b=f.read_bytes();payloads.append({'path':f.relative_to(p).as_posix(),'bytes':len(b),'sha256':sha(b)})
manifest={'payloads':payloads};pinbytes=(json.dumps(manifest,indent=2)+'\n').encode();(p/'pins.json').write_bytes(pinbytes)
seal={'pins_sha256':sha(pinbytes),'pins_bytes':len(pinbytes),'payload_count':len(payloads),'exact_file_count':len(payloads)+2};sealbytes=(json.dumps(seal,indent=2)+'\n').encode();(p/'FROZEN.json').write_bytes(sealbytes)
# WRITE HALT. Verification below is read only.
assert {f.relative_to(p).as_posix() for f in p.rglob('*') if f.is_file()}=={r['path'] for r in payloads}|{'pins.json','FROZEN.json'}
for r in payloads:check_pin(r)
report=(p/'report-final.md').read_bytes()
print(json.dumps({'status':'SEALED_WRITE_HALT','payload_count':len(payloads),'exact_file_count':len(payloads)+2,'source_wholes':len(idx['sources']),'literal_source_cuts':cuts,'report':{'path':str(p/'report-final.md'),'bytes':len(report),'sha256':sha(report)},'pins':{'path':str(p/'pins.json'),'bytes':len(pinbytes),'sha256':sha(pinbytes)},'seal':{'path':str(p/'FROZEN.json'),'bytes':len(sealbytes),'sha256':sha(sealbytes)}},indent=2))
