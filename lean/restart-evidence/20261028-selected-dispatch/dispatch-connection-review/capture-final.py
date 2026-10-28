from pathlib import Path
import hashlib,json,shutil
own=Path(__file__).parent;base=own.parent;repo=Path('/home/tritlo/Code/mcfta');lean=repo/'lean/MicroCFTA'
def sha(d):return hashlib.sha256(d).hexdigest()
def pinfo(p):
 d=p.read_bytes();return {'path':str(p.relative_to(own)),'bytes':len(d),'sha256':sha(d)}
def copy(src,dst):
 dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst);return pinfo(dst)
index=json.loads((own/'source-index.json').read_text())
for r in index['sources']:
 src=Path(r['source']);d=src.read_bytes();whole=own/r['whole']['path'];whole.write_bytes(d);r['whole']=pinfo(whole);r['bytes']=len(d);r['sha256']=sha(d)
 for c in r['cuts']:
  a,b=c['first_line'],c['last_line'];lines=d.splitlines(keepends=True);assert b<=len(lines)
  cut=own/c['path'];cut.write_bytes(b''.join(lines[a-1:b]));c.update(pinfo(cut));c['source_sha256']=sha(d)
# Focused current Haskell source corroborates only the documented operation order.
src=repo/'cfta/src/Data/CFTA/Enumeration.hs';d=src.read_bytes();lines=d.splitlines(keepends=True);cs=[]
for a,b in [(383,402),(712,736),(780,805),(858,914)]:
 p=own/'cuts'/f'Enumeration.hs.L{a}-L{b}.txt';p.write_bytes(b''.join(lines[a-1:b]));cs.append({**pinfo(p),'first_line':a,'last_line':b,'source_sha256':sha(d)})
index['sources'].append({'source':str(src),'bytes':len(d),'sha256':sha(d),'cuts':cs,'inspection':'Only the literal four listed source cuts were inspected. No Haskell execution or whole-file review is claimed.'})
# Copy actual checks, including failed attempts and final builds/public output.
commands=json.loads((base/'actual-commands.json').read_text());attempts=[]
for entry in commands:
 name=entry['name'];src=base/name;dst=own/'checks'/name
 shutil.copytree(src,dst,dirs_exist_ok=True)
 r=json.loads((dst/'report.json').read_text());assert r==entry['report']
 raw=(dst/'raw.log').read_bytes();assert len(raw)==r['bytes'] and sha(raw)==r['sha256']
 attempts.append({'folder':name,'exit_code':r['exit_code'],'raw_bytes':len(raw),'raw_sha256':sha(raw),'source_sha256':r.get('source_sha256'),'cgroup_limits':r['cgroup_limits']})
 for srcfile in src.rglob('*.lean'):
  local=dst/srcfile.relative_to(src);snapshot=local.read_bytes();index['sources'].append({'source':str(srcfile),'bytes':len(snapshot),'sha256':sha(snapshot),'whole':pinfo(local),'cuts':[],'inspection':'Compiler/check source snapshot retained verbatim. Final module sources were reviewed in full; failed source lineage was compared with its actual raw diagnostics.'})
(own/'checks/status.json').write_text(json.dumps({'attempts':attempts,'command_count':len(attempts),'failed_commands':sum(x['exit_code']!=0 for x in attempts),'reviewer_reran_checks':False,'inspection':'All six full failed raw logs were inspected after their checks. Root performed all Lean/build/public commands.'},indent=2)+'\n')
for name in ['modules.json','strict-checks.json','source-head.txt','published-base.txt','source-commits.json','source-validation.json','preservation-validation.json','public-validation.json','public-declarations.json','new-public-declarations.json','public-definitions.json','actual-commands.json','root-contract-comparisons.json','document-validation.json','audit-import-insertion.json','new-public-blocks.txt']:
 copy(base/name,own/'final-evidence'/name)
# The inherited command is not included in the current command count.
shutil.copytree(base/'prior-public-readback',own/'inherited-prior-public',dirs_exist_ok=True)
prior=(own/'inherited-prior-public/raw.log').read_bytes();actual=(own/'checks/public-readback-final/raw.log').read_bytes();new=(own/'final-evidence/new-public-blocks.txt').read_bytes()
assert prior+new==actual
(own/'final-evidence/public-prefix-independent.json').write_text(json.dumps({'status':'pass','prior_bytes':len(prior),'prior_sha256':sha(prior),'current_bytes':len(actual),'current_sha256':sha(actual),'new_bytes':len(new),'new_sha256':sha(new),'prior_plus_whole_new_appendix_equals_current':True,'inherited_command_excluded_from_current_command_count':True},indent=2)+'\n')
# Exact document insertion cuts and old-body inverses; no whole old-body review.
rows=json.loads((base/'document-validation.json').read_text());docresults=[];commons=[]
for r in rows:
 src=repo/r['path'];d=src.read_bytes();assert len(d)==r['bytes'] and sha(d)==r['sha256']
 if 'offset' not in r:
  whole=own/'documents'/r['path'];copy(src,whole)
  index['sources'].append({'source':str(src),'bytes':len(d),'sha256':sha(d),'whole':pinfo(whole),'cuts':[],'inspection':'Whole final new note inspected. Only the historical-document insertion cuts are claimed below.'})
  docresults.append({'path':r['path'],'status':'pass','new_note':True,'bytes':len(d),'sha256':sha(d)})
  continue
 a=r['offset'];z=a+r['inserted_bytes'];insert=d[a:z];old=d[:a]+d[z:]
 priorbody=(base/'prior-documents'/r['path']).read_bytes();assert old==priorbody
 assert len(old)==r['prior_bytes'] and sha(old)==r['prior_sha256']
 assert a==0 or d[a-1:a]==b'\n';assert not insert or insert.endswith(b'\n')
 p=own/'documents'/'insertions'/(r['path']+'.txt');p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(insert)
 first=d[:a].count(b'\n')+1;last=d[:z].count(b'\n');assert b''.join(d.splitlines(keepends=True)[first-1:last])==insert
 index['sources'].append({'source':str(src),'bytes':len(d),'sha256':sha(d),'cuts':[{**pinfo(p),'first_line':first,'last_line':last,'source_sha256':sha(d)}],'inspection':'Only the exact new inserted region was inspected. The complete old body was compared byte-for-byte with the retained prior-documents baseline; it was not read as current proof evidence.'})
 docresults.append({'path':r['path'],'status':'pass','offset':a,'inserted_bytes':len(insert),'inserted_sha256':sha(insert),'first_line':first,'last_line':last,'current_bytes':len(d),'current_sha256':sha(d),'old_bytes':len(old),'old_sha256':sha(old),'entire_old_body_equal_to_prior_baseline':True})
 if r['path']!='FINDINGS.md':commons.append(insert)
assert len(commons)==8 and len(set(commons))==1
find=next(x for x in rows if x['path']=='FINDINGS.md');fd=(repo/'FINDINGS.md').read_bytes()[find['offset']:find['offset']+find['inserted_bytes']];assert fd.startswith(commons[0])
(own/'documents/inverse-validation.json').write_text(json.dumps({'status':'pass','common_insertions_byte_equal':8,'findings_starts_with_exact_common_region':True,'records':docresults,'old_body_review_scope':'All inverse comparisons are exact byte checks. No claim that historical bodies were read in full.'},indent=2)+'\n')
# Final current identities, including doc-only opaque comment repair.
(own/'source-index.json').write_text(json.dumps(index,indent=2)+'\n')
modulepins=[]
for name in json.loads((base/'modules.json').read_text()):
 d=(lean/(name+'.lean')).read_bytes();modulepins.append({'module':name,'lines':len(d.splitlines()),'bytes':len(d),'sha256':sha(d)})
(own/'final-evidence/module-identities.json').write_text(json.dumps(modulepins,indent=2)+'\n')
print(json.dumps({'source_records':len(index['sources']),'literal_cuts':sum(len(x['cuts'])for x in index['sources']),'commands':len(attempts),'failures':sum(x['exit_code']!=0 for x in attempts),'module_lines':sum(x['lines']for x in modulepins),'module_bytes':sum(x['bytes']for x in modulepins),'document_records':len(docresults)},indent=2))
