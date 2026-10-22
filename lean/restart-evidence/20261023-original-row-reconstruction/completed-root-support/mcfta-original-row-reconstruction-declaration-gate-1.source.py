import datetime,hashlib,json,subprocess
from pathlib import Path
R=Path('/home/tritlo/Code/mcfta');H=R/'lean/restart-evidence/20261023-original-row-reconstruction';A=Path('/tmp/mcfta-original-row-reconstruction-signature-audit')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
frozen=json.loads((A/'FROZEN.json').read_text());assert frozen['status']=='FINAL_FROZEN_INDEPENDENT_EXACT_SIGNATURE_SOURCE_CLEAR' and not frozen['math_or_scope_hold']
assert sha(A/'review.md')==frozen['review_sha256']=='f84a8c7bb3792fd3f2c24d8a7dc01e52e5ce90a5bc4148c15eb6c64c5ff4de8f'
assert sha(A/'pins.json')==frozen['pins_sha256']=='5e2d99f471509af37a4b57c0ae4a6e295bb0c201c39823f1f3cca4535dc0ccb2'
pins=json.loads((A/'pins.json').read_text());assert isinstance(pins,dict) and len(pins)==103
for name,pin in pins.items():
 p=A/name;assert p.stat().st_size==pin['bytes'] and sha(p)==pin['sha256'],name
assert sha(H/'signature-plan/contracts.json')=='c2202a31a91d7df7b2440a88bd3c2654f7929d7d2d668635c02fc501625d5f04'
contracts=json.loads((H/'signature-plan/contracts.json').read_text())
for name,pin in contracts.items():
 p=H/'signature-plan'/name;assert sha(p)==pin['sha256'] and len(p.read_bytes().splitlines())==pin['lines']
subprocess.run(['/usr/bin/python3',str(H/'archive-extra.py'),str(A),'signature-audit'],check=True)
report=dict(status='ROOT_DECLARATION_REVIEW_CLEAR',observed_at=datetime.datetime.now().astimezone().isoformat(),module='MicroCFTA.SourceCurrentOriginalRowReconstruction',public_names=['ordinary_complete'],private_names=['stable_heap'],local_induction=None,local_names=['parentClosed','residentRows','closedRows','rebuilt','rebuiltSemantic','rebuildExtension','rebuiltGood','rawDone'],source_target=[250,320],source_hard_stop=350,contract_sha256=sha(H/'signature-plan/contracts.json'),contracts=[dict(path=name,lines=pin['lines'],sha256=pin['sha256']) for name,pin in contracts.items()],root_whole_exact_declarations_read=True,root_source_identities=29,root_source_cuts=47,independent_source_review='CLEAR',independent_review_sha256=frozen['review_sha256'],body_proposal_authorized=True,compiler_authorized=False,whole_goal_complete=False)
(H/'root-declaration-review.json').write_text(json.dumps(report,indent=2)+'\n')
original=H/'original-sources/Audit.original.lean.txt';assert sha(original)=='ebcc4770268c142e8fb5370dadcbf9be224276f4c7b0240c9876df55444715de'
(H/'original-source-index.json').write_text(json.dumps(dict(sources=[dict(path='lean/MicroCFTA/Audit.lean',snapshot='original-sources/Audit.original.lean.txt',lines=3128,sha256=sha(original))]),indent=2)+'\n')
with (H/'current-progress.md').open('a') as out:
 out.write('\n## Exact declaration gate\n\nRoot and independent whole declaration and47-cut source reviews pass.\nOne public ordinary_complete and one private stable_heap are authorized for a body proposal.\nAll eight scoped local types remain exact intermediate obligations.\nThe target is250 to320 total source lines with a350-line hard stop.\nA complete-source review must precede any compiler command. No H23 proof job has run.\nThe verifier needs the separately reviewed eight-local-fragment integration before activation.\nThe earlier bootstrap counts used different scopes. The manifest-derived baseline is98415files,\n3638 older MicroCFTA non-Audit Lean files,298 total Haskell files and207 active package files.\nThe count correction did not change the starting manifest and was not a failed job.\nThe whole goal remains ACTIVE.\n')
print(json.dumps(report))
