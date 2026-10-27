from pathlib import Path
from datetime import datetime
from zoneinfo import ZoneInfo
import hashlib,json,re,shutil
A=Path('/tmp/mcfta-opaque-finalizer-attachment-20261027');O=A/'stable-prefix-review'
def sha(d):return hashlib.sha256(d).hexdigest()
def save(rel,d):
 p=O/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(d);return {'snapshot':str(p),'bytes':len(d),'sha256':sha(d)}
def put(rel,x):return save(rel,(json.dumps(x,indent=2,ensure_ascii=False)+'\n').encode())
h=O/'review-revisions/pre-public';h.mkdir(parents=True,exist_ok=True)
if not (h/'source-index.json').exists():shutil.copyfile(O/'source-index.json',h/'source-index.json')
idx=json.loads((h/'source-index.json').read_text());records=idx['sources']
def capture(source,rel,scope):
 source=Path(source);data=source.read_bytes();r={'source':str(source),**save(rel,data),'scope':'whole evidence input','reviewed_scope':scope,'cuts':[]};records.append(r);return data,r
public,record=capture(A/'public-readback-final-1/raw.log','public/raw.log','whole 676-line output read in consecutive chunks 1-353 and 354-676; all seven signatures and axiom reports read')
assert len(public)==48268 and sha(public)=='eb63cd44545c988a6b73c3ee64b70fa810a291779c2cdf88636e4653841328bc'
prior,prior_record=capture(A/'prior-public-readback/raw.log','public/prior-raw.log','whole prior output retained for identity; three old literal blocks compared, historical body not reread')
lines=public.splitlines(keepends=True)
spans=[(1,188,'new full stable-prefix signature'),(189,203,'new opaque preparation fuel signature'),(204,258,'new head finalizer attachment signature'),(259,353,'new own-output attachment signature'),(354,406,'retained H6 signature'),(407,533,'retained old captured renderer signature'),(534,676,'retained flat captured renderer signature')]
for first,last,label in spans:
 c=b''.join(lines[first-1:last]);record['cuts'].append({'first_line':first,'last_line':last,**save(f'public/cuts/{first}-{last}.txt',c),'scope':'literal cut','purpose':label})
def blocks(raw):
 matches=list(re.finditer(rb'^(?:def )?MicroCFTA\.([A-Za-z0-9_.]+)(?:\s|$)',raw,re.M));out={}
 for i,m in enumerate(matches):out[m.group(1).decode()]=raw[m.start():(matches[i+1].start() if i+1<len(matches) else len(raw))]
 return out
current_blocks=blocks(public);prior_blocks=blocks(prior)
unchanged=[]
for name in ['SourceCurrentColdFiniteWarmCalls.constructed_node_calls','SourcePruningEnumerationCapturedEdge.diagonal_render_sound_current','SourceFlatPruningCapturedEdge.render_sound_current_resources']:
 assert current_blocks[name]==prior_blocks[name]
 block=current_blocks[name];save('public/unchanged/'+name+'.txt',block)
 unchanged.append({'declaration':name,'bytes':len(block),'sha256':sha(block),'byte_equal_prior':True})
assert len(current_blocks)==7
for rel in ['public-readback-final-1/report.json','public-readback-final-1/public.lean','public-validation.json','source-validation.json','source-head.txt','source-commits.json','build-finalizer-installed-1/report.json','build-finalizer-installed-1/raw.log']:
 capture(A/rel,'checkpoint-final/'+rel,'whole final metadata/report/command source read or exact source identity retained; actual receipt scope is explicit in review')
# Validate actual existing build and strict-Audit records already retained in previous phase.
for name in ['build-aggregate-final','strict-audit-final-1']:
 report=json.loads((A/name/'report.json').read_text());raw=(A/name/'raw.log').read_bytes()
 assert report['exit_code']==0 and report['bytes']==len(raw) and report['sha256']==sha(raw)
 if name=='build-aggregate-final':assert b'4153 jobs' in raw and b'79492 MicroCFTA theorems' in raw
 else:assert raw==b'Checked axiom dependencies of 79492 MicroCFTA theorems.\n'
validation=json.loads((A/'public-validation.json').read_text())
assert validation['status']=='pass' and validation['theorem_signatures_and_axiom_checks']==7 and validation['new_public_theorems']==4 and validation['printed_data_declarations']==0
assert set(validation['axioms'])=={'Classical.choice','Quot.sound','propext'}
put('public-review.json',{'status':'CLEAR','reviewed_at':datetime.now(ZoneInfo('Europe/Stockholm')).isoformat(),'public_bytes':len(public),'public_sha256':sha(public),'whole_lines_read':[[1,353],[354,676]],'seven_full_signatures':True,'four_new_theorems':True,'full_data_definitions':0,'axioms':validation['axioms'],'unchanged_blocks':unchanged,'installed_modules':3,'installed_module_lines':484,'aggregate_jobs':4153,'audit_dependency_count':79492,'strict_audit_raw_bytes':56,'prose_review':'pending, no seal yet'})
put('source-index.json',{'schema':'whole sources and explicit literal cuts','cut_convention':'one-based inclusive lines; splitlines(keepends=True); original LF bytes retained','sources':records})
print(json.dumps({'status':'CLEAR / OPEN','source_records':len(records),'cuts':sum(len(r['cuts']) for r in records),'public_sha256':sha(public),'unchanged_blocks':unchanged},indent=2))
