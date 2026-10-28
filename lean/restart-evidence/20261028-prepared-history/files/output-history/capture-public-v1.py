from pathlib import Path
import json,hashlib
stage=Path('/tmp/mcfta-prepared-history-20261028');own=stage/'output-history';repo=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA')
def sha(b):return hashlib.sha256(b).hexdigest()
def cp(rel,dest=None):
    src=stage/rel;dst=own/(dest or 'integration/v1/'+rel);dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(src.read_bytes());return dst
# Preserve exact rich receipt source and actual successful check.
name='SourcePruningEnumerationPreparedHeadAdmission.lean';source=repo/name;b=source.read_bytes();assert sha(b)=='3ae193af46602e83dea29096acd3687ad0daee8e09acc414f5b0a77ebf4ccc7f';assert b==(own/'drafts/head-receipt-v1'/name).read_bytes();(own/'sources'/name).write_bytes(b)
idx=json.loads((own/'source-index.json').read_text());lines=b.splitlines(keepends=True);cuts=[]
for a,z in [(1,122),(123,219),(220,len(lines))]:
    cb=b''.join(lines[a-1:z]);path=f'cuts/{source.stem}-L{a}-L{z}.lean';(own/path).write_bytes(cb);cuts.append({'path':path,'bytes':len(cb),'sha256':sha(cb),'first_line':a,'last_line':z})
idx['sources'].append({'source':str(source),'whole':{'path':'sources/'+name,'bytes':len(b),'sha256':sha(b)},'cuts':cuts,'scope':'WHOLE actual rich prepared-head admission, certificate, original full packet wrapper and proof read. Original handle and prepared parent remain separate explicit indexes; no semantic equivalence assumed.'});(own/'source-index.json').write_text(json.dumps(idx,indent=2)+'\n')
for src in sorted((stage/'prepared-head-receipt-v1').rglob('*')):
    if src.is_file() and src.suffix not in ['.olean','.ilean']:
        cp(str(src.relative_to(stage)),'checks/'+str(src.relative_to(stage)))
check=json.loads((stage/'prepared-head-receipt-v1/report.json').read_text());assert check['exit_code']==0 and check['source_sha256']==sha(b) and (stage/'prepared-head-receipt-v1/raw.log').read_bytes()==b''
assert (stage/'prepared-head-receipt-v1/MicroCFTA'/name).read_bytes()==b
(own/'head-receipt-checked-v1.json').write_text(json.dumps({'status':'PASS','source_bytes':len(b),'source_lines':len(lines),'source_sha256':sha(b),'strict_exit_code':0,'strict_raw_bytes':0,'candidate_checked_installed_identical':True,'owner_compiler_commands':0,'entire_original_declaration_retained_bytes':4615,'entire_original_declaration_sha256':'d1d0b4332770bbc4818c182a7dbe54e5d127651857f72f01cf383cd410598127','existing_Complete_IH_retained':True,'bundle':'OPEN for final docs/seal cue'},indent=2)+'\n')
# Preserve every assigned whole printed definition or theorem/axiom block.
index=json.loads((stage/'root-review/public-blocks/arity_meaning-index.json').read_text());raw=(stage/'public-readback-final/raw.log').read_bytes();prior=(stage/'prior-public-readback/raw.log').read_bytes();appendix=(stage/'new-public-blocks.txt').read_bytes();assert raw==prior+appendix
records=[]
for r in index:
    block=(stage/r['path']).read_bytes();assert len(block)==r['bytes'] and sha(block)==r['sha256'];assert appendix[r['offset']:r['offset']+len(block)]==block
    start=len(prior)+r['offset'];assert raw[start:start+len(block)]==block
    path='public-blocks/'+Path(r['path']).name;cp(r['path'],path)
    record={**r,'path':path,'raw_first_byte':start,'raw_last_byte_exclusive':start+len(block),'raw_first_line':raw[:start].count(b'\n')+1,'raw_last_line':raw[:start+len(block)].count(b'\n'),'review':'WHOLE assigned print read; complete constructor/field body for definitions, signature+full axiom list for theorems'}
    records.append(record)
assert len(records)==11 and sum(r['bytes'] for r in records)==66605
(own/'public-read-scopes-v1.json').write_text(json.dumps({'blocks':records,'whole_blocks':11,'printed_definitions':4,'theorem_signatures_and_axioms':7,'whole_bytes':sum(r['bytes'] for r in records),'whole_lines':sum((own/r['path']).read_bytes().count(b'\n') for r in records),'raw_bytes':len(raw),'raw_sha256':sha(raw),'exact_prior_prefix_bytes':len(prior),'new_appendix_bytes':len(appendix),'new_appendix_sha256':sha(appendix),'axiom_scope':'Each theorem uses a subset of propext/Classical.choice/Quot.sound. receipt_output_invocation and finish_hook_outputs list only propext.','review_scope':'Only these11wholeblocks are semantically reviewed here. Other new catalogue blocks are preserved as provenance, not claimed reviewed.'},indent=2)+'\n')
for rel in ['root-review/public-blocks/arity_meaning-index.json','public-validation.json','source-validation.json','audit-summary.json','modules.json','strict-checks.json','new-public-blocks.txt','public-readback-final/public.lean','public-readback-final/report.json','public-readback-final/raw.log','public-readback-final/inputs.json','prior-public-readback/report.json','prior-public-readback/raw.log']:
    cp(rel)
for folder in ['audit-build','audit-strict']:
    for src in sorted((stage/folder).rglob('*')):
        if src.is_file() and src.suffix not in ['.olean','.ilean']:cp(str(src.relative_to(stage)))
print(json.dumps({'status':'PASS','assigned_blocks':len(records),'assigned_bytes':sum(r['bytes'] for r in records),'assigned_lines':sum((own/r['path']).read_bytes().count(b'\n') for r in records),'head_source_sha256':sha(b),'bundle_status':'OPEN'},indent=2))
