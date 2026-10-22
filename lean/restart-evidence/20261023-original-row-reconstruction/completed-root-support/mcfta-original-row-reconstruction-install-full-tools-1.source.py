import ast,datetime,hashlib,json,re,subprocess
from pathlib import Path
R=Path('/home/tritlo/Code/mcfta');H=R/'lean/restart-evidence/20261023-original-row-reconstruction'
T=Path('/tmp/mcfta-original-row-reconstruction-checkpoint-prep');I=Path('/tmp/mcfta-original-row-reconstruction-local-fragment-integration')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
packages=[(Path('/tmp/mcfta-original-row-reconstruction-checkpoint-audit'),'checkpoint-audit','9405d88b63307bfe511a620d1e5bede027dedc7d056bb7205d68a72d91389000',82),(I,'declaration-integration','3c619d0b4ccff2b431bbd2927fa0fb29924fae19b6f20532fa412406ffcbe12f',25),(Path('/tmp/mcfta-original-row-reconstruction-integration-audit'),'integration-audit','831941f6357e2380937c67be68016d31d0f6ba99c14db17d7a45370c08cedc28',34)]
for package,name,pins_sha,count in packages:
 assert (package/'FROZEN.json').is_file() and sha(package/'pins.json')==pins_sha
 pins=json.loads((package/'pins.json').read_text());assert isinstance(pins,dict) and len(pins)==count
 for path,pin in pins.items():
  p=package/path;assert p.stat().st_size==pin['bytes'] and sha(p)==pin['sha256'],p
 subprocess.run(['/usr/bin/python3',str(H/'archive-extra.py'),str(package),name],check=True)
assert sha(I/'verify-proofs.py')=='2bf1df9b5bd04fc2a08a0e5610cc9b7b83dd0cb195d76b4c3027fdd843c040b4'
old=(T/'verify-proofs.py').read_text();new=(I/'verify-proofs.py').read_text()
start=old.index('assert next(iter(contracts))');end=old.index('public = re.findall',start)
new_start=new.index('assert list(contracts)');new_end=new.index('public = re.findall',new_start)
assert old[:start]==new[:new_start] and old[end:]==new[new_end:]
assert len(new.splitlines())==297 and sum(isinstance(n,ast.Assert) for n in ast.walk(ast.parse(new)))==137
binding=json.loads((I/'early-full-preparation/declaration-bindings.json').read_text())
facts=binding['exact_three_declaration_facts'];assert facts=={'__H23_MODULE_NAME__':'SourceCurrentOriginalRowReconstruction','__H23_PUBLIC_SPECS_JSON__':[['ordinary_complete','theorem']],'__H23_SOURCE_HARD_STOP__':350}
for name,pin in binding['selected'].items():
 data=(T/name).read_text()
 for token,value in facts.items():
  if isinstance(value,list):data=data.replace('"'+token+'"',repr(json.dumps(value)))
  else:data=data.replace(token,str(value))
 p=I/'early-full-preparation'/name;assert p.read_text()==data and sha(p)==pin['sha256'] and len(data.splitlines())==pin['lines']
 assert not re.search(r'__H23_[A-Z0-9_]+__',data)
 ast.parse(data)
 assert not (H/name).exists()
subprocess.run(['/usr/bin/python3',str(H/'archive-extra.py'),str(I/'early-full-preparation'),'full-preparation'],check=True)
for name in binding['selected']:(H/name).write_bytes((I/'early-full-preparation'/name).read_bytes())
report=dict(status='ROOT_ACCEPTED_DECLARATION_BOUND_FULL_TOOLS',observed_at=datetime.datetime.now().astimezone().isoformat(),root_whole_early_full_sources_read=True,root_whole_original_tools_and_exact_verifier_delta_read=True,independent_source_review='CLEAR',independent_review_sha256='6cb3306c7d5a40cc6fbe2296c44b8354c165ffc5aed74009f1b4b5c99d54fc1f',selected_early_full_tools=binding['selected'],exact_declaration_facts=facts,composite_tool_lines=1037,composite_assertions=332,verifier_evidence_binding_still_pending=True,verifier_activated=False,mathematical_source_compiler_gate_still_required=True,new_proof_jobs=0)
(H/'root-full-tools-review.json').write_text(json.dumps(report,indent=2)+'\n')
with (H/'current-progress.md').open('a') as out:
 out.write('\n## Reviewed declaration integration\n\nRoot and independent source reviews pass for the twelve pending tools and the separate\neight-local-fragment verifier overlay. All four contract pins remain. The composite has\n1037 tool source lines and332 assertions. This source integration was not a failed job.\nOnly the declaration-bound reader, materializer and unchanged capped runner are installed.\nAll actual proof metrics and the nine-tool evidence binding remain pending.\nNo mathematical source has compiled. Complete body review remains required.\n')
print(json.dumps(report))
