from pathlib import Path
import json,hashlib,shutil
stage=Path('/tmp/mcfta-prepared-composition-20261028');own=stage/'sibling-origins'
def sha(b):return hashlib.sha256(b).hexdigest()
def cp(rel,dest=None):
    src=stage/rel;dst=own/(dest or ('integration/'+rel));dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(src.read_bytes());return dst
index=json.loads((stage/'public-blocks-index.json').read_text());names=['SourcePruningEnumerationPreparedFiniteSiblingResources.alternatives_finite_complete_resources_origins','SourcePruningEnumerationPreparedFiniteSiblingResources.parent_finite_complete_resources_origins','SourcePruningEnumerationPreparedRecursive.receipt_finite_complete_resources_origins']
raw=(stage/'public-readback-final/raw.log').read_bytes();prior=(stage/'prior-public-readback/raw.log').read_bytes();assert raw[:len(prior)]==prior
report=json.loads((stage/'public-readback-final/report.json').read_text());assert report['exit_code']==0 and report['bytes']==len(raw) and report['sha256']==sha(raw)
blocks=[]
for rec in index:
    if rec['name'] not in names:continue
    b=(stage/rec['path']).read_bytes();assert len(b)==rec['bytes'] and sha(b)==rec['sha256'];assert b'\xe2\x80\xa6' not in b
    start=raw.index(b);assert raw.find(b,start+1)==-1
    path='public-blocks/'+Path(rec['path']).name;cp(rec['path'],path)
    blocks.append({**rec,'path':path,'raw_first_byte':start,'raw_last_byte_exclusive':start+len(b),'first_line':raw[:start].count(b'\n')+1,'last_line':raw[:start+len(b)].count(b'\n'),'review':'WHOLE printed statement and axiom list read; not all unrelated public catalogue statements','axioms':['propext','Classical.choice','Quot.sound']})
for rel in ['public-blocks-index.json','public-validation.json','source-validation.json','audit-summary.json','source-head.txt','modules.json','strict-checks.json','new-public-blocks.txt','prior-public-readback/raw.log','prior-public-readback/report.json','prior-public-readback/public.lean','public-readback-final/inputs.json','public-readback-final/public.lean','public-readback-final/raw.log','public-readback-final/report.json']:
    cp(rel)
for folder in ['audit-build','audit-strict']:
    for p in sorted((stage/folder).rglob('*')):
        if p.is_file() and p.suffix not in ['.olean','.ilean']:
            cp(str(p.relative_to(stage)))
(own/'public-read-scopes-v1.json').write_text(json.dumps({'blocks':blocks,'whole_assigned_blocks':3,'whole_assigned_lines':sum((own/b['path']).read_bytes().count(b'\n') for b in blocks),'whole_assigned_bytes':sum(b['bytes'] for b in blocks),'raw_bytes':len(raw),'raw_sha256':sha(raw),'exact_inherited_prefix_bytes':len(prior),'inherited_prefix_sha256':sha(prior),'new_appendix_bytes':len(raw)-len(prior),'new_appendix_sha256':sha(raw[len(prior):]),'review_scope':'Only these three whole new statement/axiom blocks and their exact raw offsets are semantically reviewed; the complete public raw log is preserved for provenance/prefix equality.'},indent=2)+'\n')
print(json.dumps({'assigned_blocks':len(blocks),'assigned_bytes':sum(b['bytes'] for b in blocks),'raw_bytes':len(raw),'prior_prefix_exact':True,'status':'PASS'},indent=2))
