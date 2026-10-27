from pathlib import Path
import hashlib,json,shutil,re
repo=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-head-policy-20261028');out=area/'encoding-origin-review'
def sha(b):return hashlib.sha256(b).hexdigest()
def record(p):
 b=p.read_bytes();return {'path':str(p),'bytes':len(b),'sha256':sha(b)}
def putjson(p,v):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(v,indent=2)+'\n')
def copy(src,dst):dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst)
index=json.loads((out/'source-index.json').read_text())
for s in index['sources']:
 b=Path(s['source']).read_bytes();assert sha(b)==s['whole']['sha256']
 for cut in s['cuts']:
  assert Path(cut['path']).read_bytes()==b''.join(b.splitlines(True)[cut['first_line']-1:cut['last_line']])
def add_source(rel,spans,scope):
 src=repo/rel;b=src.read_bytes();dst=out/'sources'/rel;copy(src,dst);cuts=[]
 for first,last in spans:
  cut=out/'cuts'/rel/f'{first}-{last}.txt';data=b''.join(b.splitlines(True)[first-1:last]);cut.parent.mkdir(parents=True,exist_ok=True);cut.write_bytes(data)
  cuts.append({**record(cut),'first_line':first,'last_line':last})
 index['sources'].append({'source':str(src),'whole':record(dst),'cuts':cuts,'reviewed_scope':scope})
add_source('lean/MicroCFTA/SourcePruningAssignmentRefutation.lean',[(14,31)],'Whole new34line proof and actual full public signature read.')
add_source('lean/MicroCFTA/SourcePruningEnumerationFiniteHeadCoverage.lean',[(34,54),(62,116)],'Original entire declaration compared literally to the new grouped old packet; implementation body not reread this turn.')
add_source('lean/notes-current-accepted-head-policy.md',[(28,49),(59,69),(129,161)],'Whole final10410byte note read. New strongest local claim, filter scope, checks, and Haskell boundary reviewed.')
# Copy all16 actual compiler/build/public check receipts. Preserve exact checked source inputs.
check_dirs=sorted(p for p in area.iterdir() if p.is_dir() and (p/'report.json').is_file())
assert len(check_dirs)==16,len(check_dirs)
checks=[]
for src in check_dirs:
 r=json.loads((src/'report.json').read_text());raw=(src/'raw.log').read_bytes();assert len(raw)==r['bytes'] and sha(raw)==r['sha256'];assert r['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
 for p in src.rglob('*'):
  if p.is_file() and p.suffix not in ['.olean','.ilean','.c','.o']:
   copy(p,out/'checks'/src.name/p.relative_to(src))
 checks.append({'name':src.name,**r})
assert sum(r['exit_code']!=0 for r in checks)==7
putjson(out/'checks-summary.json',{'status':'PASS','actual_commands':16,'failed_attempts':7,'standalone_strict_flags':'warningAsError=true and linter.all=true','all_measured_memory_max_and_high':4294967296,'all_measured_swap_max':0,'checks':checks})
metadata=['modules.json','source-head.txt','source-validation.json','public-validation.json','public-prefix-comparison.json','preservation-validation.json','root-contract-comparisons.json','document-validation.json','document-paths.json','literal-callback-refutation-return.txt','literal-head-policy-declaration.txt','literal-original-head-declaration.txt']
for name in metadata:copy(area/name,out/'integration'/name)
for name in ['contract-v1.py','noncompiler-failures.txt']:copy(area/'helper-drafts'/name,out/'integration/helper-drafts'/name)
# Independently reproduce the exact declaration recovery without running any proof tool.
def statement(module,name):
 s=(repo/'lean/MicroCFTA'/f'{module}.lean').read_text();return s[s.index('theorem '+name):s.index(' := by')]
old=statement('SourcePruningEnumerationFiniteHeadCoverage','head_finite_complete_resources_accepting');policy=statement('SourcePruningEnumerationAcceptedHeadPolicy','head_finite_complete_resources_policy');cb=statement('SourcePruningEnumerationAcceptedHeadCallback','head_finite_complete_resources_callback_policy');marker=' :\n    ∃ (bound : Nat)'
op,ob=old.split(marker,1);np,nb=policy.split(marker,1);cp,cbbody=cb.split(marker,1)
assert np.replace('head_finite_complete_resources_policy','head_finite_complete_resources_accepting')==op
names,oldbody=ob.split(',\n      ',1);newnames,newbody=nb.split(',\n      ',1);cbnames,cbreturn=cbbody.split(',\n      ',1)
assert names==newnames==cbnames and newbody.startswith('('+oldbody+') ∧\n')
assert cp.replace('head_finite_complete_resources_callback_policy','head_finite_complete_resources_policy')==np and cbreturn.startswith('('+newbody+') ∧\n')
original=statement('SourcePruningEnumerationCallbackRefutation','callback_prefix_complete_resources_refutes').split('    ∃ fuel result after,\n',1)[1]
replacements=json.loads((area/'root-contract-comparisons.json').read_text())['callback']['token_substitutions']
converted=re.sub(r'\b('+'|'.join(re.escape(x) for x in replacements)+r')\b',lambda m:replacements[m.group()],original)
assert cbreturn.count('('+converted.strip()+') ∧\n')==1
putjson(out/'independent-contract-recovery.json',{'status':'PASS','old_head_entire_declaration_bytes':len(old.encode()),'old_head_entire_declaration_sha256':sha(old.encode()),'previous_policy_entire_declaration_bytes':len(policy.encode()),'previous_policy_entire_declaration_sha256':sha(policy.encode()),'original_callback_return_bytes':len(original.encode()),'original_callback_return_sha256':sha(original.encode()),'mapping':replacements,'whitespace_rule':'Generator strips the inserted callback block before outer grouping. No operational or logical tokens changed.','bounds_before_all_model_observers':True})
# Validate the old public byte prefix without rereading its old text; read all new blocks.
public=(area/'public-readback-1/raw.log').read_bytes();prior=(area/'prior-public-readback/raw.log').read_bytes();new=(area/'new-public-blocks.txt').read_bytes()
assert public==prior+new;assert len(new)==51903;assert b'sorryAx' not in new
copy(area/'new-public-blocks.txt',out/'integration/new-public-blocks.txt');copy(area/'prior-public-readback/raw.log',out/'integration/prior-public-readback/raw.log')
putjson(out/'public-review.json',{'status':'CLEAR','reviewed':'All four new full theorem/axiom blocks,655lines. Old prefix validated as bytes; old signatures were not all reread.','new':record(out/'integration/new-public-blocks.txt'),'prior_prefix':record(out/'integration/prior-public-readback/raw.log'),'entire_public_bytes':len(public),'entire_public_sha256':sha(public),'allowed_axioms':['propext','Classical.choice','Quot.sound'],'no_new_runtime_definitions':True})
# Preserve old bodies and exact insertions. Do not claim old body text was reread.
doc_records=[];common=None
for meta in json.loads((area/'document-validation.json').read_text()):
 if 'inserted_bytes' not in meta:continue
 rel=meta['path'];current=(repo/rel).read_bytes();old=(area/'prior-documents'/rel).read_bytes();off=meta['offset'];count=meta['inserted_bytes'];insert=current[off:off+count]
 assert len(current)==meta['bytes'] and sha(current)==meta['sha256'];assert current[:off]+current[off+count:]==old;assert len(old)==meta['old_bytes'] and sha(old)==meta['old_sha256']
 if common is None:common=insert
 assert insert.startswith(common)
 old_copy=out/'documents/prior'/rel;copy(area/'prior-documents'/rel,old_copy)
 inserted=out/'documents/insertions'/f'{rel}.insert';inserted.parent.mkdir(parents=True,exist_ok=True);inserted.write_bytes(insert)
 first=current[:off].count(b'\n')+1;last=first+insert.count(b'\n')-1
 assert current[:off].endswith(b'\n') and insert.endswith(b'\n')
 # Cuts-only source identity. Reconstruction supplies the full exact current bytes.
 index['sources'].append({'source':str(repo/rel),'bytes':len(current),'sha256':sha(current),'cuts':[{**record(inserted),'first_line':first,'last_line':last}],'reviewed_scope':'Entire new insertion read. Complete old body copied and inverse byte-verified; historical text not reread.'})
 doc_records.append({'source':str(repo/rel),'current_bytes':len(current),'current_sha256':sha(current),'offset':off,'old':record(old_copy),'insert':record(inserted),'whole_old_body_preserved':True,'first_line':first,'last_line':last})
assert len(doc_records)==9
putjson(out/'document-reconstruction.json',{'status':'PASS','common_prefix_bytes':len(common),'common_prefix_sha256':sha(common),'all_nine_start_with_same_prefix':True,'records':doc_records,'review_scope':'Whole new note and all current insertions read. Old historical bodies only compared and preserved as bytes.'})
putjson(out/'source-index.json',index)
putjson(out/'check-status-final.json',{'status':'CLEAR; final scope complete; ready to seal','source_head':'5e8098180a8737fe641949ce6cd493cad73a9278','native_grammar_origin':'OPEN; no full Context counterexample instantiated','public':'PASS253theoremblocks+5olddefinitions; all249priorblocks exactprefix','docs':'Whole finalnote and nine insertions CLEAR; inverses verified','future_progress':'No emitted output, stuck exclusion, complete recursion coverage, archive or publication result claimed'})
print('CAPTURE PASS',len(index['sources']),'source identities',sum(len(x['cuts']) for x in index['sources']),'cuts',len(checks),'checks')
