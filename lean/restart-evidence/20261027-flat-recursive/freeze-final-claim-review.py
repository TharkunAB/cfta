from pathlib import Path
import json, hashlib, re, datetime
repo=Path('/home/tritlo/Code/mcfta'); area=Path('/tmp/mcfta-flat-recursive-20261027'); out=area/'final-claim-review'
assert not out.exists(), 'preserve any existing review'
out.mkdir()
def sha(b):return hashlib.sha256(b).hexdigest()
def dump(rel,obj):
 p=out/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(obj,indent=2,ensure_ascii=False)+'\n')
def put(rel,b):
 p=out/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
def pin(path,rel,role,scope='whole source reviewed'):
 b=path.read_bytes();put(rel,b)
 return dict(path=str(path),source=str(path),snapshot=rel,bytes=len(b),sha256=sha(b),lines=len(b.splitlines()),role=role,read_scope=scope)
modules=json.loads((area/'modules.json').read_text()); checks=json.loads((area/'strict-checks.json').read_text());sources=[];evidence=[];cuts=[];docs=[];valid=[]
for name in modules:
 path=repo/'lean/MicroCFTA'/(name+'.lean');b=path.read_bytes();s=sources.append(pin(path,'inputs/lean/MicroCFTA/'+path.name,'new checked module'))
 folder=area/checks[name];report=json.loads((folder/'report.json').read_text());raw=(folder/'raw.log').read_bytes();snapshot=folder/'MicroCFTA'/(name+'.lean')
 assert snapshot.read_bytes()==b and report['source_sha256']==sha(b)
 assert report['exit_code']==0 and raw==b'' and report['sha256']==sha(raw)
 assert '-DwarningAsError=true' in report['command'] and '-Dlinter.all=true' in report['command']
 valid.append(dict(module=name,check=checks[name],source_sha256=sha(b),exact_strict_input=True,literal_empty_raw=True))
for name,expected in [('SourceCurrentColdFiniteWarmCalls','e4665b0bb522ec88f1925fe6bc360b76e9e4bdfbe6192210ac708a3097a20cc5'),('SourcePruningEnumerationCapturedRendering','18a81a7cdf0b208021f9ad5097e616270ad6001dbc75b08a7901352d5e174386')]:
 p=repo/'lean/MicroCFTA'/(name+'.lean');assert sha(p.read_bytes())==expected
 sources.append(pin(p,'inputs/lean/MicroCFTA/'+p.name,'unchanged global theorem','whole-file identity; established global boundary, no new proof claim'))
for name in ['SourcePruningEnumerationFiniteContract','SourcePruningEnumerationFiniteResources']:
 p=repo/'lean/MicroCFTA'/(name+'.lean');sources.append(pin(p,'inputs/lean/MicroCFTA/'+p.name,'original contract comparison','public contract compared with new complete induction'))
def header_cut(name,decl):
 p=repo/'lean/MicroCFTA'/(name+'.lean');b=p.read_bytes();lines=b.splitlines(keepends=True)
 start=next(i for i,x in enumerate(lines) if re.match(rb'(?:theorem|def) '+decl.encode()+rb'\b',x));end=start
 while b':=' not in lines[end]:end+=1
 if lines[end].rstrip().endswith(b':='):
  pass
 payload=b''.join(lines[start:end+1]);rel='cuts/'+name+'--'+decl+'.lean';put(rel,payload)
 cuts.append(dict(path=str(p),source=str(p),snapshot=rel,start=start+1,end=end+1,bytes=len(payload),sha256=sha(payload),source_sha256=sha(b),role='literal declaration header'))
for name,decl in [('SourceFlatPruningRecursiveFiniteResources','finite_complete'),('SourceFlatPruningRecursiveFiniteResources','run_finite_complete_resources'),('SourceFlatPruningFiniteContract','Complete'),('SourcePruningEnumerationFiniteContract','Complete'),('SourcePruningEnumerationFiniteResources','run_finite_complete_resources')]:header_cut(name,decl)
common=None
for d in json.loads((area/'document-validation.json').read_text()):
 p=repo/d['path'];b=p.read_bytes();assert len(b)==d['bytes'] and sha(b)==d['sha256']
 if 'offset' in d:
  start=d['offset'];end=start+d['inserted_bytes'];part=b[start:end]
  if common is None:common=part
  assert part==common
  prior=area/'prior-documents'/d['path'];old=prior.read_bytes();assert b[:start]+b[end:]==old
  rel='documents/prefixes/'+d['path'];put(rel,part)
  docs.append(dict(path=str(p),source=str(p),snapshot=rel,source_bytes=len(b),source_sha256=sha(b),byte_start=start,byte_end_exclusive=end,bytes=len(part),sha256=sha(part),start=len(b[:start].splitlines())+1,end=len(b[:end].splitlines()),read_scope='inserted prefix only; historical text not reread',removal_reproduces_prior=True,prior_source=str(prior),prior_bytes=len(old),prior_sha256=sha(old)))
 else:docs.append(pin(p,'documents/'+d['path'],'new current note','whole note read'))
put('documents/common-prefix.md',common)
for module,folder in checks.items():
 for n in ['report.json','raw.log']:
  p=area/folder/n;evidence.append(pin(p,'evidence/'+folder+'/'+n,'actual strict evidence','report/source hash/exit/raw validation'))
for folder in ['build-aggregate','public-readback']:
 for n in ['report.json','raw.log']:
  p=area/folder/n;evidence.append(pin(p,'evidence/'+folder+'/'+n,'actual installed evidence','report and structural validation; public full text not manually reread'))
 r=json.loads((area/folder/'report.json').read_text());raw=(area/folder/'raw.log').read_bytes();assert r['exit_code']==0 and r['bytes']==len(raw) and r['sha256']==sha(raw)
for n in ['public.lean']:
 p=area/'public-readback'/n;evidence.append(pin(p,'evidence/public-readback/'+n,'installed readback request','readback request and declared API coverage'))
for n in ['modules.json','source-validation.json','source-totals.json','strict-checks.json','public-validation.json','public-declarations.json','public-definitions.json','source-commits.json','source-head.txt','document-validation.json','document-paths.json']:
 p=area/n;evidence.append(pin(p,'evidence/'+n,'current checkpoint control','current control correlated with pinned inputs'))
pv=json.loads((area/'public-validation.json').read_text());assert pv['bytes']==256463 and pv['sha256']==sha((area/'public-readback/raw.log').read_bytes()) and pv['theorem_signatures_and_axiom_checks']==37 and pv['definitions']==11 and pv['no_elision'] is True
assert pv['axioms']==['propext','Classical.choice','Quot.sound']
aggregate=(area/'build-aggregate/raw.log').read_text();assert '4064' in aggregate and '78977' in aggregate
report='''[2026-10-27 09:04 CET] FINAL CLEAR. Source-only independent claim review.

The reviewed source head is 4b0400e958911d86bcd1953250d1484086a75eff. All 22 new module conclusions and their proof composition were reviewed. Every live module equals its successful strict input. No concrete semantic blocker or unsupported claim was found in the new note or nine status prefixes.

The strongest new result is SourceFlatPruningRecursive.run_finite_complete_resources. Its original inputs include the current Packet, numeric Fits, native guard carrier, selector membership and length laws, a suspended-mass ceiling and a finite recursive reservation. These inputs derive one work bound and one stable original outcome before quantification over related flat caches. Every related initial flat cache and every larger work bound has an actual flat recursive outcome related to that same original outcome. The complete original OutcomeResources certificate is retained. The depth induction discharges the stronger recursive Complete hypothesis. The final theorem has no future flat-success, post-hook Ranges, Canonical or desired semantic-result premise.

The callback proof obtains the original callback receipt once before the universal flat input. Pointwise callback replay then uses the smaller-depth induction at the actual framed returned cache. Native and representative action closures can vary with fuel. The proof retains actual phase inputs and endpoints; it does not assert global equality of those closures or of the whole prepared Result.

Head and sibling composition retains the same actual receipt, Post, full Memos and native endpoint. A later sibling starts at the actual post-hook Caller and query state. The enumeration cache and metadata are restored from the captured input for each sibling. Ordered relation constructors retain receipt and output order, including duplicates. Completed outputs retain metadata, branch caches, Caller and Queries. Explicit exhausted and unsupported stops retain structured diagnostics, output prefixes, nested reasons and optional endpoints. Valid rejection keeps its actual effects and cache observation. It does not acquire a Safe or accepted-output claim.

Child, traversal, selected-edge and captured-edge resource wrappers retain their original conclusion packets and resource fields, followed by the coupled actual flat execution family. Their original bounds are chosen before the flat input. Own allocation order, staged optional actions, residual completion and captured-slot finalization use the same actual receipts. The continuation and recursive layers consume those families; they do not replace actual subtree or callback execution with an identity hook or an assumed successful endpoint.

The whole new note was read. Each of the nine 1874-byte inserted prefixes was read and compared. All nine are identical. Removing each inserted region reproduces its preserved original document byte-for-byte. Only the literal inserted regions are copied here; historical document prose was not reread. The note and prefixes accurately distinguish adequate-bound finite-depth correspondence from unbounded convergence. They retain the outstanding output-language soundness and coverage, pruning policy, initial admission histories, semantic consumer gates and physical Haskell correspondence gaps. The checkpoint changes no Haskell source and adds no native-test claim.

Actual retained evidence records 23 successful strict checks, including Audit, with warningAsError and all linters. The 22 new module logs are literally empty. Audit aggregate passes 4064 jobs and 78977 dependency checks. Its inherited unused-input warning is not a new-source failure. Installed public validation passes 37 full theorem signatures and axiom checks, including 35 new declarations and the two unchanged globals, plus 11 definitions. The 256463-byte public output has SHA256 45874645e31499d9dc945a86db71c0df6c41e5529d4c33147cc9318b9077f502. Its validator reports no elision and only propext, Classical.choice and Quot.sound. This review correlates source conclusions, requests and structural public validation; it does not claim a separate manual reading of every expanded public-output byte. No checks were rerun by this reviewer.

The strongest global language theorem remains H6. Its whole-source SHA256 is e4665b0bb522ec88f1925fe6bc360b76e9e4bdfbe6192210ac708a3097a20cc5. CapturedRendering remains 18a81a7cdf0b208021f9ad5097e616270ad6001dbc75b08a7901352d5e174386. Both identities are unchanged. The new result permits explicit finite-capacity stops. It proves neither unbounded convergence nor semantic output acceptance, coverage or physical Haskell certification. No future archive, seal or push is inferred.
'''
put('report.txt',report.encode())
validation=dict(status='pass',new_modules=len(modules),source_lines=3956,public_theorems=35,definitions=11,strict_checks=len(checks),strict_sources=valid,identical_document_prefixes=9,prefix_bytes=len(common),document_removal_exact=True,global_theorems_unchanged=True,review_scope='source and data only; no builds, Git or repository edits',public_read_scope='source conclusions and structural installed validator, not manual full expanded public output')
dump('validation.json',validation)
dump('source-pins.json',dict(version=1,status='FINAL CLEAR',observed_at='2026-10-27 09:04 CET',sources=sources,cuts=cuts,documents=docs,evidence=evidence,validation='validation.json',read_scope='22 source conclusions and composition; original finite contracts; final note and inserted prefixes; evidence as labeled'))
# Verify every copied payload and every still-current original before freezing.
for record in sources+evidence:
 b=Path(record['source']).read_bytes();assert sha(b)==record['sha256'] and (out/record['snapshot']).read_bytes()==b
for record in cuts:
 b=Path(record['source']).read_bytes();assert sha(b)==record['source_sha256'];assert (out/record['snapshot']).read_bytes()==b''.join(b.splitlines(keepends=True)[record['start']-1:record['end']])
entries=[]
for p in sorted(out.rglob('*')):
 if p.is_file():entries.append(dict(path=str(p.relative_to(out)),bytes=p.stat().st_size,sha256=sha(p.read_bytes())))
dump('pins.json',dict(version=1,pins=entries,count=len(entries)))
pp=(out/'pins.json').read_bytes();dump('FROZEN.json',dict(status='FINAL CLEAR',payload_count=len(entries),file_count=len(entries)+2,pins_bytes=len(pp),pins_sha256=sha(pp),report_sha256=sha((out/'report.txt').read_bytes()),source_pins_sha256=sha((out/'source-pins.json').read_bytes()),sources=len(sources),new_modules=len(modules),cuts=len(cuts),cut_lines=sum(x['end']-x['start']+1 for x in cuts),documents=len(docs),evidence=len(evidence)))
print(json.dumps(json.loads((out/'FROZEN.json').read_text()),indent=2));print('FROZEN_sha256',sha((out/'FROZEN.json').read_bytes()))
