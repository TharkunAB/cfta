from pathlib import Path
import json,hashlib,datetime
from zoneinfo import ZoneInfo
base=Path('/tmp/mcfta-traversal-coverage-20261027/owner');root=Path('/home/tritlo/Code/mcfta');stage=base.parent
sha=lambda b:hashlib.sha256(b).hexdigest()
inputs={
'SourcePruningEnumerationTraversalResources.lean':[(31,87),(102,164),(165,230)],
'SourcePruningEnumerationTraversalCompletion.lean':[(19,78),(112,145)],
'SourcePruningEnumerationChildCoverage.lean':[(35,123),(124,203)],
'SourcePruningEnumerationChildTraversal.lean':[(14,38),(40,68)],
'EnumerationCorrectness.lean':[(644,649),(705,727),(755,776)],
'EnumerationConstruction.lean':[(44,49),(84,127)],
'Language.lean':[(22,45)]}
sources=[]
for name,cuts in inputs.items():
 src=root/'lean/MicroCFTA'/name;full=src.read_bytes();snapshot='inputs/'+name;(base/snapshot).write_bytes(full)
 item={'source':str(src),'snapshot':snapshot,'bytes':len(full),'sha256':sha(full),'cuts':[]}
 for a,b in cuts:
  assert b<=len(full.splitlines(keepends=True));d=b''.join(full.splitlines(keepends=True)[a-1:b]);snap=f'cuts/{src.stem}.{a}-{b}.lean.txt';(base/snap).write_bytes(d)
  item['cuts'].append({'snapshot':snap,'first_line':a,'last_line':b,'bytes':len(d),'sha256':sha(d),'source_sha256':sha(full)})
 sources.append(item)
old=(root/'lean/MicroCFTA/SourcePruningEnumerationTraversalResources.lean').read_text();new=(base/'drafts/v1/SourcePruningEnumerationTraversalCoverage.lean').read_text()
def stmt(text,name):
 a=text.index('theorem '+name);return text[a:text.index(' := by',a)]
o=stmt(old,'complete_with_fragments_resources');n=stmt(new,'complete_with_fragments_resources_accepting');i=n.index(' ∧\n      ∀ (ambient : InternedGuardedLanguage.Env Symbol)');r=n[:i].replace('theorem complete_with_fragments_resources_accepting','theorem complete_with_fragments_resources',1);assert o==r
for name,text in [('original-full-statement.txt',o),('recovered-full-statement.txt',r)]: (base/'contracts'/name).write_text(text)
comparison={'status':'PASS','old_theorem':'MicroCFTA.SourcePruningEnumerationTraversalCompletion.complete_with_fragments_resources','new_theorem':'MicroCFTA.SourcePruningEnumerationTraversalCompletion.complete_with_fragments_resources_accepting','original':'contracts/original-full-statement.txt','recovered':'contracts/recovered-full-statement.txt','bytes':len(o.encode()),'sha256':sha(o.encode()),'mapping':['Remove only the final model/ordered-terms assignment-extension observer.','Restore only the original theorem name. All admission, existential witnesses and full result conjunction remain literal.'],'public_new_definitions':0,'child_accepting_producer_sites':new.count('SourcePruningEnumerationChildCompletion.complete_with_fragments_resources_accepting '),'old_traversal_producer_calls':new.count('\n    complete_with_fragments_resources seed')}
assert comparison['child_accepting_producer_sites']==1 and comparison['old_traversal_producer_calls']==0
(base/'contracts/comparison.json').write_text(json.dumps(comparison,indent=2)+'\n')
# Preserve actual first failure; this does not invoke a compiler.
evidence=[]
for name in ['report.json','raw.log','MicroCFTA/SourcePruningEnumerationTraversalCoverage.lean']:
 src=stage/'strict-traversal-coverage-1'/name;data=src.read_bytes();snap='evidence/strict-traversal-coverage-1/'+name;out=base/snap;out.parent.mkdir(parents=True,exist_ok=True);out.write_bytes(data);evidence.append({'source':str(src),'snapshot':snap,'bytes':len(data),'sha256':sha(data)})
report=json.loads((stage/'strict-traversal-coverage-1/report.json').read_text());assert report['exit_code']==1 and report['bytes']==23630 and report['source_sha256']==sha(new.encode())
metadata={'status':'OPEN','recorded_at':datetime.datetime.now(ZoneInfo('Europe/Stockholm')).isoformat(),'drafts':[{'revision':'v1','snapshot':'drafts/v1/SourcePruningEnumerationTraversalCoverage.lean','bytes':len(new.encode()),'lines':len(new.splitlines()),'sha256':sha(new.encode()),'initial_status':'UNCOMPILED on submission','actual_status':'ROOT STRICT1 FAIL','failure':'Only final result-match rewrite motive depends on tailRun/tailShape/tailAccepting; all other proof clauses elaborated. Root owns v2 proof-only substitution repair.'}],'evidence':evidence,'line_convention':'one-based inclusive, original LF retained','compiler_owner':'Root; none run by this worker'}
(base/'attempts.json').write_text(json.dumps(metadata,indent=2)+'\n')
(base/'source-index.json').write_text(json.dumps({'status':'OPEN','line_convention':'one-based inclusive, original LF retained','sources':sources},indent=2)+'\n')
print(json.dumps({'whole_sources':len(sources),'literal_cuts':sum(len(x['cuts']) for x in sources),'old_statement_bytes':len(o.encode()),'old_statement_sha256':sha(o.encode()),'draft_sha256':sha(new.encode())},indent=2))
