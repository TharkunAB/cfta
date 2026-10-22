import ast,hashlib,json,subprocess
from pathlib import Path
R=Path('/home/tritlo/Code/mcfta');H=R/'lean/restart-evidence/20261023-original-row-reconstruction'
S=Path('/tmp/mcfta-original-row-reconstruction-signature');T=Path('/tmp/mcfta-original-row-reconstruction-checkpoint-prep')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(S/'pins.json')=='e3fcbc7cc1d848369ac09189867b89d126cadcd9a43cc1dfa8a1ee2bb8c18e8f'
assert sha(T/'pins.json')=='29846bf88d4646ce3fe9e7d819efa40bf69f83794cd8bfc61484e6b73cbf74ba'
sp=json.loads((S/'pins.json').read_text());tp=json.loads((T/'pins.json').read_text())
assert isinstance(sp,list) and len(sp)==99 and isinstance(tp,dict) and len(tp)==73
for item in sp:
 p=S/item['path'];assert p.stat().st_size==item['bytes'] and sha(p)==item['sha256'],item['path']
for name,item in tp.items():
 p=T/name;assert p.stat().st_size==item['bytes'] and sha(p)==item['sha256'],name
index=json.loads((S/'source-index.json').read_text());assert len(index['sources'])==29
cuts=0;lines=0
for item in index['sources']:
 p=Path(item['path']);data=p.read_bytes()
 assert sha(p)==item['sha256'] and data==(S/item['snapshot']).read_bytes() and len(data)==item['bytes'] and len(data.splitlines())==item['lines'],p
 for cut in item['cuts']:
  actual=b''.join(data.splitlines(True)[cut['start']-1:cut['end']]);snapshot=S/cut['snapshot']
  assert snapshot.read_bytes()==actual and sha(snapshot)==cut['sha256'] and len(actual)==cut['bytes'],snapshot
  cuts+=1;lines+=cut['end']-cut['start']+1
assert cuts==47 and lines==715
paths=json.loads((S/'import-paths.json').read_text())
for chain in paths['used_primary_import_paths'].values():
 assert chain[0] in paths['direct_imports']
 for first,second in zip(chain,chain[1:]):
  p=R/'lean'/Path(*first.split('.')).with_suffix('.lean')
  assert 'import '+second in p.read_text().splitlines(),(first,second)
scripts=json.loads((T/'selected-scripts.json').read_text())['scripts'];total=assertions=0
for name,pin in scripts.items():
 p=T/name;data=p.read_bytes();tree=ast.parse(data)
 assert sha(p)==pin['sha256'] and len(data.splitlines())==pin['lines']
 assert sum(isinstance(n,ast.Assert) for n in ast.walk(tree))==pin['assertions']
 assert (T/'predecessors'/name).read_bytes()==(R/'lean/restart-evidence/20261022-original-row-group-chain'/name).read_bytes()
 total+=pin['lines'];assertions+=pin['assertions']
assert len(scripts)==12 and total==1019 and assertions==327
for package,name in [(S,'signature-plan'),(T,'checkpoint-preparation')]:
 subprocess.run(['/usr/bin/python3',str(H/'archive-extra.py'),str(package),name],check=True)
report=dict(status='ROOT_WHOLE_SOURCE_READ_PENDING_INDEPENDENT_GATES',signature_pins=99,tool_pins=73,source_identities=29,source_cuts=47,source_cut_lines=715,whole_dependency_manual_read_claimed=False,whole_context_private_public_and_local_statements_read=True,whole_tool_sources_read=True,tool_lines=total,tool_assertions=assertions,local_fragment_integration_required_before_verifier_activation=True,compiler_authorized=False,body_authorized=False,new_proof_jobs=0)
(H/'root-preparation-read-scope.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report))
