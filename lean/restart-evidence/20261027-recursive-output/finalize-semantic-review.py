from pathlib import Path
from datetime import datetime
import json, hashlib, re
repo=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-recursive-output-20261027');out=area/'semantic-review'
assert not (out/'FROZEN.json').exists()
def sha(b):return hashlib.sha256(b).hexdigest()
def put(rel,b):
 p=out/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
def dump(rel,o):put(rel,(json.dumps(o,indent=2,ensure_ascii=False)+'\n').encode())
def pin(p,rel,role,scope):
 b=p.read_bytes();put(rel,b);return dict(path=str(p),source=str(p),snapshot=rel,bytes=len(b),sha256=sha(b),role=role,read_scope=scope)
modules=json.loads((area/'modules.json').read_text());checks=json.loads((area/'strict-checks.json').read_text());assert len(modules)==9
sources=[];cuts=[];docs=[];evidence=[];validation=[]
for name in modules:
 p=repo/'lean/MicroCFTA'/(name+'.lean');b=p.read_bytes();folder=area/checks[name];r=json.loads((folder/'report.json').read_text());raw=(folder/'raw.log').read_bytes()
 assert r['exit_code']==0 and r['source_sha256']==sha(b) and raw==b'' and r['sha256']==sha(raw)
 assert (folder/'MicroCFTA'/p.name).read_bytes()==b
 assert '-DwarningAsError=true' in r['command'] and '-Dlinter.all=true' in r['command']
 sources.append(pin(p,'inputs/lean/MicroCFTA/'+p.name,'new checked module','whole current source reviewed'))
 validation.append(dict(module=name,strict=checks[name],sha256=sha(b),exact_strict_source=True,literal_empty_raw=True))
for name in ['SourcePruningEnumerationRendering','SourcePruningEnumerationRecursivePacket','EnumerationFlatSemantics','FlatUnionFind','SourceFlatPruningRecursiveFiniteResources']:
 p=repo/'lean/MicroCFTA'/(name+'.lean');sources.append(pin(p,'inputs/lean/MicroCFTA/'+p.name,'actual semantic dependency','focused definitions and theorem contracts reviewed'))
for name,expected in [('SourceCurrentColdFiniteWarmCalls','e4665b0bb522ec88f1925fe6bc360b76e9e4bdfbe6192210ac708a3097a20cc5'),('SourcePruningEnumerationCapturedRendering','18a81a7cdf0b208021f9ad5097e616270ad6001dbc75b08a7901352d5e174386')]:
 p=repo/'lean/MicroCFTA'/(name+'.lean');assert sha(p.read_bytes())==expected
 sources.append(pin(p,'inputs/lean/MicroCFTA/'+p.name,'unchanged global theorem','whole-file identity; no new proof claim'))
def header(name,decl):
 p=repo/'lean/MicroCFTA'/(name+'.lean');b=p.read_bytes();lines=b.splitlines(keepends=True)
 start=next(i for i,x in enumerate(lines) if re.match(rb'theorem '+decl.encode()+rb'\b',x));end=start
 while b':=' not in lines[end]:end+=1
 cut(name,start+1,end+1,decl)
def cut(name,start,end,label):
 p=repo/'lean/MicroCFTA'/(name+'.lean');b=p.read_bytes();part=b''.join(b.splitlines(keepends=True)[start-1:end]);rel=f'cuts/{name}--{label}.lean';put(rel,part)
 cuts.append(dict(path=str(p),source=str(p),snapshot=rel,start=start,end=end,bytes=len(part),sha256=sha(part),source_sha256=sha(b)))
for name,decl in [('SourceFlatPruningOutputFrontier','decision_none_iff'),('SourceFlatPruningOutputFrontier','decision_done_iff'),('SourceFlatPruningOutputFrontier','candidates_nil_iff_native_frontier'),('SourceFlatPruningRecursiveOutputOrigin','run_output_origin'),('SourceFlatPruningRecursiveOutputResources','run_finite_complete_output_resources'),('SourceFlatPruningRenderingReplay','render_replays'),('SourceFlatPruningRenderingAssignment','render_assignment'),('SourceFlatPruningRecursiveOutputRendering','output_render_assignment'),('SourceFlatPruningRecursiveOutputCompletion','output_done_frontier'),('SourceFlatPruningRecursiveOutputCompletion','run_finite_complete_output_certificates')]:header(name,decl)
cut('SourceFlatPruningRendering',19,54,'direct-runtime')
cut('SourcePruningEnumerationRendering',23,25,'discharged')
cut('SourceFlatPruningRecursiveOutputOrigin',26,32,'origin')
cut('SourceFlatPruningRecursiveOutputResources',30,42,'own-output-resource-definition')
common=None
for d in json.loads((area/'document-validation.json').read_text()):
 p=repo/d['path'];b=p.read_bytes();assert sha(b)==d['sha256'] and len(b)==d['bytes']
 if 'offset' in d:
  start=d['offset'];end=start+d['inserted_bytes'];part=b[start:end]
  if common is None:common=part
  assert part==common
  old=area/'prior-documents'/d['path'];oldbytes=old.read_bytes();assert b[:start]+b[end:]==oldbytes
  rel='documents/prefixes/'+d['path'];put(rel,part)
  docs.append(dict(path=str(p),source=str(p),snapshot=rel,source_bytes=len(b),source_sha256=sha(b),byte_start=start,byte_end_exclusive=end,bytes=len(part),sha256=sha(part),read_scope='inserted region only; historical prose not reread',prior_source=str(old),prior_bytes=len(oldbytes),prior_sha256=sha(oldbytes),removal_exact=True))
 else:docs.append(pin(p,'documents/'+d['path'],'new note','whole note read'))
assert len(docs)==10
put('documents/common-prefix.md',common)
for name,folder in checks.items():
 r=json.loads((area/folder/'report.json').read_text());raw=(area/folder/'raw.log').read_bytes();assert r['exit_code']==0 and r['bytes']==len(raw) and r['sha256']==sha(raw)
 assert r['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
 for n in ['report.json','raw.log']:evidence.append(pin(area/folder/n,'evidence/'+folder+'/'+n,'actual strict report','report/raw/source equality validation'))
for folder in ['build-aggregate','public-readback']:
 r=json.loads((area/folder/'report.json').read_text());raw=(area/folder/'raw.log').read_bytes();assert r['exit_code']==0 and r['bytes']==len(raw) and r['sha256']==sha(raw)
 for n in ['report.json','raw.log']:evidence.append(pin(area/folder/n,'evidence/'+folder+'/'+n,'actual installed validation','report and structural validation; not manual whole expanded public-output reading'))
for n in ['modules.json','strict-checks.json','source-validation.json','source-totals.json','public-validation.json','public-declarations.json','public-definitions.json','source-commits.json','source-head.txt','document-validation.json','document-paths.json']:
 p=area/n
 if p.exists():evidence.append(pin(p,'evidence/'+n,'checkpoint control','control correlated with actual sources/evidence'))
pub=json.loads((area/'public-validation.json').read_text());totals=json.loads((area/'source-totals.json').read_text());assert pub['status']=='pass' and pub['no_elision'] and pub['axioms']==['propext','Classical.choice','Quot.sound']
assert sha((area/'public-readback/raw.log').read_bytes())==pub['sha256']
head=(area/'source-head.txt').read_text().strip();now=datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
oldreport=(out/'report.txt').read_text();body=oldreport.split('\n\n',2)[2]
report=f'[{now}] FINAL CLEAR. Independent source, output-certificate and current-claim review. Source head {head}.\n\nAll nine new module sources and conclusions are CLEAR. Each live file equals its successful strict input and has an empty raw log. No concrete semantic blocker or unsupported strongest claim was found.\n\n'+body
report+='\nThe final new note was read whole. The nine literal inserted status prefixes were read and are identical. Removing each region reproduces its preserved original bytes. The bundle copies only those regions, not the historical document bodies. Current prose keeps the output assignment result conditional and does not claim original-input acceptance, done-to-discharge, unbounded convergence or physical Haskell certification.\n'
report+=f"\nActual retained validation records {totals['modules']} new modules, {totals['lines']} lines, {totals['public_theorems']} public theorems and {totals['public_definitions']} runtime definitions. The strict mapping has {len(checks)} passing checks including Audit. Installed public validation records {pub['theorem_signatures_and_axiom_checks']} full signatures and axiom checks, {pub['definitions']} definitions, {pub['bytes']} bytes and SHA256 {pub['sha256']}. It reports no elision and only propext, Classical.choice and Quot.sound. This review correlates source contracts and structural public validation; it does not claim a manual reading of every expanded public-output byte. The aggregate report/raw are pinned as actual passing evidence. No checks were rerun by this reviewer.\n"
report+='\nThe actual aggregate raw log records 4073 jobs and 79112 theorem dependency checks. Its inherited unused-input warning is retained. No native tests were rerun for these Lean-only additions.\n'
report+='\nH6 remains e4665b0bb522ec88f1925fe6bc360b76e9e4bdfbe6192210ac708a3097a20cc5. CapturedRendering remains 18a81a7cdf0b208021f9ad5097e616270ad6001dbc75b08a7901352d5e174386. Both live files match these unchanged identities. No future archive, seal or publication is inferred.\n'
put('report.txt',report.encode())
dump('source-pins.json',dict(version=1,status='FINAL CLEAR',observed_at=now,sources=sources,cuts=cuts,documents=docs,evidence=evidence,read_scope='nine full current modules; focused actual semantic dependencies; final note and literal prefixes; evidence as labeled'))
dump('validation.json',dict(status='pass',strict_sources=validation,identical_prefixes=9,exact_removal=True,unchanged_globals=True))
for record in sources+evidence:
 assert sha(Path(record['source']).read_bytes())==record['sha256'];assert (out/record['snapshot']).read_bytes()==Path(record['source']).read_bytes()
entries=[]
for p in sorted(out.rglob('*')):
 if p.is_file():entries.append(dict(path=str(p.relative_to(out)),bytes=p.stat().st_size,sha256=sha(p.read_bytes())))
dump('pins.json',dict(version=1,pins=entries,count=len(entries)))
b=(out/'pins.json').read_bytes();dump('FROZEN.json',dict(status='FINAL CLEAR',payload_count=len(entries),file_count=len(entries)+2,pins_bytes=len(b),pins_sha256=sha(b),report_sha256=sha((out/'report.txt').read_bytes()),source_pins_sha256=sha((out/'source-pins.json').read_bytes()),sources=len(sources),new_modules=len(modules),cuts=len(cuts),cut_lines=sum(x['end']-x['start']+1 for x in cuts),documents=len(docs),evidence=len(evidence)))
print((out/'FROZEN.json').read_text());print('FROZEN_SHA256',sha((out/'FROZEN.json').read_bytes()))
