from pathlib import Path
import hashlib,json
A=Path('/tmp/mcfta-prepared-models-20261028');O=A/'ordinary-head-models';R=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA')
def sha(b):return hashlib.sha256(b).hexdigest()
def save(p,b):
 p.parent.mkdir(parents=True,exist_ok=True)
 if p.exists():assert p.read_bytes()==b,p
 else:p.write_bytes(b)
 return {'path':str(p),'bytes':len(b),'sha256':sha(b)}
p=A/'sibling-models-v1';rep=json.loads((p/'report.json').read_text());raw=(p/'raw.log').read_bytes();assert rep['exit_code']==0 and rep['bytes']==len(raw)==0 and rep['sha256']==sha(raw)
name='SourcePruningEnumerationPreparedFiniteSiblingCoverage.lean';tested=p/'MicroCFTA'/name;candidate=O/'drafts/sibling-v2'/name;installed=R/name
assert tested.read_bytes()==candidate.read_bytes()==installed.read_bytes();assert sha(tested.read_bytes())==rep['source_sha256']
for q in [p/'report.json',p/'raw.log',tested]:save(O/'evidence/sibling-models-v1'/q.relative_to(p),q.read_bytes())
x=json.loads((O/'source-index.json').read_text());b=installed.read_bytes();lines=b.splitlines(keepends=True)
rec={'source':str(installed),'whole':save(O/'sources'/f'{name}.{sha(b)[:12]}.whole',b),'cuts':[{**save(O/'cuts'/f'{name}.{sha(b)[:12]}.L1-L{len(lines)}.txt',b),'first_line':1,'last_line':len(lines)}],'read_scope':'WHOLE actual indexed sibling proof reviewed against the entire old reference induction and each explicit new-worker/forecast/admission change. Installed, owned immutable and strict snapshot bytes match.'}
assert not any(r['source']==str(installed) for r in x['sources']);x['sources'].append(rec);(O/'source-index.json').write_text(json.dumps(x,indent=2)+'\n')
status={'status':'PASS first actual strict check of exact sibling-v2; root sole compiler','report':rep,'installed_and_immutable_and_tested_source_bytes_equal':True,'original_admission_complete_removed_and_derived_by_each_actual_head':True,'new_semantic_producer_inputs':[],'bundle_state':'OPEN; aggregate/public/docs pending'}
(O/'checked-sibling-status.json').write_text(json.dumps(status,indent=2)+'\n')
q=O/'report-open.md';text=q.read_text();save(O/'report-revisions/report-before-sibling-pass.md',text.encode())
text=text.replace('The prepared head observer is checked by Root. The sibling extension is a source-only candidate awaiting Root\'s compiler result.','The prepared head and sibling observers are checked by Root. Both use the actual new worker and retain their complete existing resource results.')
text=text.replace('## New prepared sibling candidate','## Checked prepared sibling extension')
text=text.replace('Current candidate: drafts/sibling-v2/','Checked source: drafts/sibling-v2/')
text=text.replace('It is UNTESTED until an actual Root receipt is supplied.','Root checked these exact bytes in sibling-models-v1. The first actual strict check passes with an empty raw log. Its tested snapshot, installed source and immutable sibling-v2 source match exactly. The actual report records warningAsError/all linters, measured 4 GiB memory.max/high and zero swap. The earlier sibling-v1 remains source-only and untested.')
text=text.replace('The sibling result would add a real indexed chosen-event-or-earlier-hook-stop law.','The sibling result adds a real indexed chosen-event-or-earlier-hook-stop law.')
q.write_text(text)
print('PASS',rep['source_sha256'],len(x['sources']),'source records; bundle OPEN')
