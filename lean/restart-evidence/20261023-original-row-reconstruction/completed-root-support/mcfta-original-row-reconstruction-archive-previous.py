import hashlib,json,shutil,subprocess
from pathlib import Path
R=Path('/home/tritlo/Code/mcfta');H=R/'lean/restart-evidence/20261023-original-row-reconstruction';P=R/'lean/restart-evidence/20261022-original-row-group-chain'
base=json.loads((H/'starting-files.json').read_text());counts=json.loads((H/'baseline-counts.json').read_text())
counts['older_non_audit_lean']=sum(p.startswith('lean/MicroCFTA/') and p.endswith('.lean') and p!='lean/MicroCFTA/Audit.lean' for p in base)
counts['haskell_files']=sum(p.endswith('.hs') for p in base)
counts['active_package_files']=sum(p.split('/')[0] in {'cfta','cfta-generator','cfta-ghc','decision-model'} for p in base)
assert counts['baseline_files']==98415 and counts['older_non_audit_lean']==3638 and counts['haskell_files']==298 and counts['active_package_files']==207
counts['count_scope']='Older Lean means lean/MicroCFTA except Audit. Haskell means all baseline .hs, including retained archives.'
(H/'baseline-counts.json').write_text(json.dumps(counts,indent=2)+'\n')
D=H/'previous-local-checkpoint';assert not D.exists();D.mkdir();files={}
for p in sorted(Path('/tmp').glob('mcfta-original-row-group-chain-*')):
 if p.is_file() and not (P/'completed-root-support'/p.name).exists():
  shutil.copyfile(p,D/p.name);files[p.name]=hashlib.sha256(p.read_bytes()).hexdigest()
(D/'manifest.json').write_text(json.dumps(files,indent=2)+'\n')
registry=json.loads((H/'archived-components.json').read_text());assert 'previous-local-checkpoint' not in registry
registry['previous-local-checkpoint']={str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(D.rglob('*')) if p.is_file()}
(H/'archived-components.json').write_text(json.dumps(registry,indent=2)+'\n')
(H/'previous-local-checkpoint.json').write_bytes(Path('/tmp/mcfta-original-row-group-chain-local-publication.json').read_bytes())
(H/'previous-authorized-push.json').write_bytes(Path('/tmp/mcfta-original-row-group-chain-authorized-push.json').read_bytes())
(H/'original-sources').mkdir();(H/'original-sources/Audit.original.lean.txt').write_bytes((R/'lean/MicroCFTA/Audit.lean').read_bytes())
(H/'haskell-repair-index.md').write_bytes((P/'haskell-repair-index.md').read_bytes())
print(json.dumps(dict(status='PASS',baseline_counts=counts,previous_postseal_support_files=len(files))))
