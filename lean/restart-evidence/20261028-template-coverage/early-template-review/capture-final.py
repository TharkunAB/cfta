from pathlib import Path
import hashlib,json,shutil
repo=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-template-coverage-20261027');base=area/'early-template-review'
def sha(b):return hashlib.sha256(b).hexdigest()
def record(p):
 b=p.read_bytes();return {'path':str(p),'bytes':len(b),'sha256':sha(b)}
def save(src,dest):
 dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(src.read_bytes());return record(dest)
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
index=json.loads((base/'source-index.json').read_text())
old=repo/'lean/MicroCFTA/SourcePruningEnumerationCallbackResources.lean'
new=repo/'lean/MicroCFTA/SourcePruningEnumerationCallbackRefutation.lean'
literal=(area/'literal-callback-old-contract.txt').read_bytes()
olddata=old.read_text();newdata=new.read_text()
assert literal.decode() in olddata and literal.decode().lstrip() in newdata
params=olddata[olddata.index('    (holeKey'):olddata.index(' :\n    ∃ fuel result after')]
assert params in newdata
assert newdata.index('∃ fuel result after')<newdata.index('∀ (language :')
assert newdata[newdata.index(' := by'):].count('callback_prefix_complete_resources formulas')==1
olddecl=olddata[olddata.index('theorem callback_prefix_complete_resources'):olddata.index(' := by')]
assert len(olddecl.encode())==3691
save(area/'literal-callback-old-contract.txt',base/'evidence/literal-callback-old-return.txt')
(base/'evidence/literal-callback-old-declaration.txt').write_text(olddecl)
dump(base/'callback-final-contract-comparison.json',{'original_parameters_literal':True,'old_return_conjunction_literal_except_initial_indentation':True,'old_return_bytes':len(literal),'old_return_sha256':sha(literal),'old_declaration_bytes':len(olddecl.encode()),'old_declaration_sha256':sha(olddecl.encode()),'producer_calls':1,'fixed_execution_precedes_all_models':True,'final_source':record(new),'historical_v2_model_before_bound_is_superseded':True})
validation=json.loads((area/'source-validation.json').read_text());assert validation['status']=='pass'
modules=json.loads((area/'modules.json').read_text());assert len(modules)==11
assert sum(len((repo/'lean/MicroCFTA'/f'{m}.lean').read_bytes()) for m in modules)==78553
assert sum(len((repo/'lean/MicroCFTA'/f'{m}.lean').read_bytes().splitlines()) for m in modules)==1352
reviewed_new={'SourcePruningStructuralTemplateMeaning','SourcePruningProgramSemantics','SourcePruningGroupsRefutation','SourcePruningEarlyRefutation','SourcePruningOracleRefutation','SourcePruningRecordTypesRefutation','SourcePruningEnumerationCallbackRefutation'}
existing={e['source'] for e in index['sources']}
for check in validation['strict_checks']:
 name=check['check'];out=base/'checks'/name;out.mkdir(parents=True,exist_ok=True)
 for f in ['report.json','raw.log']:save(area/name/f,out/f)
 report=json.loads((out/'report.json').read_text());assert report['exit_code']==0;assert record(out/'raw.log')['sha256']==report['sha256']
 snap=area/name/'MicroCFTA'/f"{check['module']}.lean";save(snap,out/snap.name)
 assert record(out/snap.name)['sha256']==report['source_sha256']==check['sha256']
 src=repo/'lean/MicroCFTA'/snap.name;assert src.read_bytes()==snap.read_bytes()
 if str(src) not in existing and check['module']!='Audit':
  dest=base/'sources/lean/MicroCFTA'/src.name;save(src,dest);entry={'source':str(src),'whole':record(dest),'cuts':[],'reviewed_scope':'Whole final proof read.' if check['module'] in reviewed_new else 'All installed public signatures and semantic definitions read. Whole proof body is not independently reviewed here.'}
  text=src.read_text();lines=src.read_bytes().splitlines(keepends=True)
  if check['module']=='SourcePruningEnumerationCallbackRefutation':spans=[(40,47),(86,108)]
  else:
   start=text.index('theorem ');end=text.index(' := by',start);spans=[(text[:start].count('\n')+1,text[:end].count('\n')+1)]
  for a,z in spans:
   z=min(z,len(lines));cut=base/'cuts/lean/MicroCFTA'/src.name/f'{a}-{z}.txt';cut.parent.mkdir(parents=True,exist_ok=True);cut.write_bytes(b''.join(lines[a-1:z]));entry['cuts'].append({**record(cut),'first_line':a,'last_line':z})
  index['sources'].append(entry);existing.add(str(src))
for name in ['audit-build-1','audit-build-2','public-readback-1','public-readback-2']:
 out=base/'checks'/name;out.mkdir(parents=True,exist_ok=True)
 for f in ['report.json','raw.log']:save(area/name/f,out/f)
 report=json.loads((out/'report.json').read_text());assert record(out/'raw.log')['sha256']==report['sha256']
 if (area/name/'public.lean').exists():
  save(area/name/'public.lean',out/'public.lean');assert record(out/'public.lean')['sha256']==report['source_sha256']
for name in ['source-validation.json','public-validation.json','public-prefix-comparison.json','preservation-validation.json','root-contract-comparisons.json','document-validation.json','document-paths.json','source-head.txt','modules.json','actual-commands.json','public-declarations.json','public-definitions.json']:
 save(area/name,base/'evidence'/name)
commands=json.loads((area/'actual-commands.json').read_text());assert len(commands)==48;assert sum(c['report']['exit_code']!=0 for c in commands)==18
for c in commands:
 r=c['report'];lim=r['cgroup_limits'];assert lim['memory.max']==lim['memory.high']=='4294967296' and lim['memory.swap.max']=='0'
 raw=area/c['name']/'raw.log';assert len(raw.read_bytes())==r['bytes'] and sha(raw.read_bytes())==r['sha256']
prior=area/'prior-public-readback/raw.log';current=area/'public-readback-2/raw.log';fresh=area/'new-public-blocks.txt'
assert len(prior.read_bytes())==971561 and current.read_bytes()==prior.read_bytes()+fresh.read_bytes()
assert len(current.read_bytes())==1003823 and len(fresh.read_bytes())==32262
save(prior,base/'evidence/prior-public-readback.raw.log');save(fresh,base/'evidence/new-public-blocks.txt')
dump(base/'public-prefix-local-verification.json',{'status':'pass','prior':record(prior),'current':record(current),'new':record(fresh),'all_prior_233_blocks_are_exact_prefix':True,'new_16_signatures_and_five_definitions_read_in_full':True})
recon=[];common=None
for r in json.loads((area/'document-validation.json').read_text()):
 src=repo/r['path'];data=src.read_bytes();assert len(data)==r['bytes'] and sha(data)==r['sha256']
 if 'offset' not in r:
  dest=base/'sources'/r['path'];save(src,dest);index['sources'].append({'source':str(src),'whole':record(dest),'cuts':[],'reviewed_scope':'Whole final 10819-byte note read.'});continue
 offset=r['offset'];size=r['inserted_bytes'];insert=data[offset:offset+size];prior_source=area/'prior-documents'/r['path'];old=prior_source.read_bytes()
 assert len(old)==r['old_bytes'] and sha(old)==r['old_sha256'];assert old[:offset]+insert+old[offset:]==data
 if common is None:common=insert
 assert insert.startswith(common)
 oldcopy=base/'documents/prior'/r['path'];insertcopy=base/'documents/insertions'/r['path'];save(prior_source,oldcopy);insertcopy.parent.mkdir(parents=True,exist_ok=True);insertcopy.write_bytes(insert)
 recon.append({'source':str(src),'prior_source':str(prior_source),'old':record(oldcopy),'insert':record(insertcopy),'offset':offset,'bytes':len(data),'sha256':sha(data),'exact_inverse_verified':True,'read_scope':'Common insertion read once and exact equality checked in every document. FINDINGS extra read in full. Historical body is byte-preserved; not reread.'})
assert len(recon)==9 and len(common)==2147
assert sum(r['insert']['bytes']!=len(common) for r in recon)==1
dump(base/'document-reconstructions.json',{'status':'pass','schema':'original-plus-insert','documents':recon,'common_prefix_bytes':len(common),'common_prefix_sha256':sha(common)})
dump(base/'source-index.json',index)
# Verify each source copy and literal cut after all captures.
for e in index['sources']:
 src=Path(e['source']);whole=Path(e['whole']['path']);assert src.read_bytes()==whole.read_bytes()
 assert record(whole)==e['whole']
 for c in e.get('cuts',[]):
  cut=Path(c['path']);lines=whole.read_bytes().splitlines(keepends=True);assert cut.read_bytes()==b''.join(lines[c['first_line']-1:c['last_line']]);assert record(cut)['sha256']==c['sha256']
dump(base/'capture-final-validation.json',{'status':'pass','sources':len(index['sources']),'cuts':sum(len(e.get('cuts',[])) for e in index['sources']),'documents':len(recon),'recorded_commands':len(commands),'recorded_failed_commands':18,'source_head':(area/'source-head.txt').read_text().strip(),'public_bytes':len(current.read_bytes()),'public_sha256':sha(current.read_bytes()),'new_public_bytes':len(fresh.read_bytes()),'new_public_sha256':sha(fresh.read_bytes()),'note_sha256':sha((repo/'lean/notes-current-template-coverage.md').read_bytes())})
print((base/'capture-final-validation.json').read_text())
