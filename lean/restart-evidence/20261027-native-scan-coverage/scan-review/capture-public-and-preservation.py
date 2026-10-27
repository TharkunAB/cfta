from pathlib import Path
import hashlib,json,re
repo=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-native-scan-coverage-20261027');out=area/'scan-review';sha=lambda b:hashlib.sha256(b).hexdigest()
def put(rel,b):
 p=out/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b.encode() if isinstance(b,str) else b)
def copy(rel,dest=None):
 b=(area/rel).read_bytes();put(dest or 'evidence/'+rel,b);return b
oldrecord=out/'reviewed-drafts/source-index-scan-v2-record.json'
if oldrecord.exists():
 row=json.loads(oldrecord.read_text());put('reviewed-drafts/scan-v2-provenance.json',json.dumps({'status':'HISTORICAL REVIEWED DRAFT; failed first strict check; final V3 separately pinned.','original_source':row['source'],'old_whole_sha256':row['whole']['sha256'],'preserved_copy':'reviewed-drafts/scan-v2.lean','initial_source_record':row},indent=2)+'\n');oldrecord.unlink()
prior=copy('prior-public-readback/raw.log');raw=(out/'evidence/public-readback-1/raw.log').read_bytes();new=copy('new-public-blocks.txt')
assert raw==prior+new
for which,b in [('prior',prior),('new',new),('all',raw)]:
 axioms=re.findall(rb"depends on axioms: \[([^\]]*)\]",b,re.S)
 allowed={b'propext',b'Classical.choice',b'Quot.sound'}
 assert all({x.strip() for x in a.split(b',')}<=allowed for a in axioms)
 assert b'...' not in b and '\u2026'.encode() not in b
 if which=='new': assert len(axioms)==3
 if which=='prior': assert len(axioms)==173
 if which=='all': assert len(axioms)==176
# Focused preserved earlier scope blocks: native H6 and whole finite rendered acceptance.
texts=raw.decode();names=['SourceCurrentColdFiniteWarmCalls.constructed_node_calls','SourcePruningEnumerationRecursive.run_finite_complete_resources_render_sound_from_initial_arity']
focused=[]
for name in names:
 start=re.search(r'^MicroCFTA\.'+re.escape(name)+r'(?=\s)',texts,re.M).start();end=re.search(r"^'MicroCFTA\."+re.escape(name)+r"' depends on axioms: \[[^\]]*\]\n",texts,re.M).end()
 block=texts[start:end];dest='public-focus/'+name+'.txt';put(dest,block);focused.append({'declaration':name,'path':dest,'bytes':len(block.encode()),'sha256':sha(block.encode()),'unchanged_in_prior_prefix':block.encode() in prior})
counts={}
for manifest in ['prior-strong-sources.json','prior-enumeration-sources.json','prior-haskell-sources.json']:
 rows=json.loads(copy(manifest))
 for r in rows:
  b=(repo/r['path']).read_bytes();assert len(b)==r['bytes'] and sha(b)==r['sha256'],r['path']
 counts[manifest]=len(rows)
audit=(repo/'lean/MicroCFTA/Audit.lean').read_bytes();before=copy('prior-sources/Audit.lean');meta=json.loads((area/'audit-import-insertion.json').read_text());addition=''.join('import MicroCFTA.'+m+'\n' for m in meta['modules']).encode();at=meta['insertion_offset'];assert audit[at:at+len(addition)]==addition;assert audit[:at]+audit[at+len(addition):]==before
for rel in ['public-validation.json','public-readback-1/public.lean','prior-public-declarations.json','prior-public-definitions.json']:copy(rel)
# The final proof repair leaves both entire old recovered propositions exact.
for module,theorem,marker in [('SourcePruningEnumerationNativeHeadCoverage','head_complete_resources_accepting',' ∧\n      ∀ (ambient'),('SourcePruningEnumerationNativeBranchCoverage','complete_with_history_resources_accepting',' ∧\n      ∀ (index : Nat) (chosen')]:
 s=(repo/'lean/MicroCFTA'/f'{module}.lean').read_text();newprop=s[s.index('theorem '+theorem+'\n'):].split(' := by\n',1)[0];recovered=newprop.rsplit(marker,1)[0].replace('theorem '+theorem,'theorem '+theorem.removesuffix('_accepting'),1);assert recovered==(out/f'contracts/{module}.original.txt').read_text()
put('evidence/independent-public-preservation.json',json.dumps({'status':'PASS','public':{'prior_bytes':len(prior),'prior_sha256':sha(prior),'old_full_blocks':173,'new_bytes':len(new),'new_sha256':sha(new),'new_full_blocks':3,'all_bytes':len(raw),'all_sha256':sha(raw),'all_blocks':176,'exact_prior_prefix':True,'std3_only':True,'no_elision':True,'full_new_blocks_read':True,'prior_focused_blocks':focused},'unchanged_sources_verified':counts,'audit_inverse':{'only_imports':meta['modules'],'exact_full_old_recovery':True,'old_bytes':len(before),'old_sha256':sha(before)},'final_head_scan_old_full_propositions_exact':True},indent=2)+'\n')
put('assembly-note.json',json.dumps({'metadata_assembly_only':True,'initial_command':'python capture-final-evidence.py','initial_result':'python executable unavailable; no Python code executed.','correction':'Use installed python3. Metadata capture and all assertions completed. No Lean compiler, build, runtime evaluation or repository edit was performed by reviewer.'},indent=2)+'\n')
print(json.dumps({'status':'PASS','public':len(raw),'prior':len(prior),'new':len(new),'unchanged':counts,'audit_exact':True}))
