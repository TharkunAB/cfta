import datetime, hashlib, json, subprocess
from pathlib import Path
R=Path('/home/tritlo/Code/mcfta')
H=R/'lean/restart-evidence/20261022-original-row-group-chain'
A=Path('/tmp/mcfta-original-row-group-chain-final-doc-audit')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
frozen=json.loads((A/'FROZEN.json').read_text())
assert frozen['status']=='FINAL_FROZEN_SOURCE_CLEAR'
assert sha(A/'review.md')==frozen['review_sha256']=='37d98e856abc4b91314c90a7614bb596d08230d8fa937f407450174984a1ec74'
assert sha(A/'pins.json')==frozen['pins_sha256']=='9cf5618e948378295d21d9bc13f112db703d6a888f03066620785e2c767e5d40'
pins=json.loads((A/'pins.json').read_text());assert isinstance(pins,list) and len(pins)==frozen['pinned_files']==99
for item in pins:
 p=A/item['path'];assert p.is_file() and p.stat().st_size==item['bytes'] and sha(p)==item['sha256'],item['path']
assert len(json.loads((H/'archived-components.json').read_text()))==19
subprocess.run(['/usr/bin/python3',str(H/'archive-extra.py'),str(A),'final-doc-audit'],check=True)
assert len(json.loads((H/'archived-components.json').read_text()))==20
report=dict(status='ROOT_ACCEPTED_FINAL_DOCUMENT_REVIEW',observed_at=datetime.datetime.now().astimezone().isoformat(),review_sha256=frozen['review_sha256'],reviewed_whole_review=True,pinned_files=99,archived_components=20,nine_document_inverses=True,findings_repair_index_first=True,proof_jobs=3,proof_failures=0,root_metadata_packaging_failures=2,next_declaration_authorized=False,next_body_authorized=False,next_compiler_authorized=False,whole_goal_complete=False,seal_publication_push_pending=True)
(H/'root-final-doc-review.json').write_text(json.dumps(report,indent=2)+'\n')
with (H/'current-progress.md').open('a') as output:
 output.write('\n## Final document review and initial preservation\n\nThe initial verification and preservation pass at the historical19-component cut.\nAll96320 baseline files/modes,3637 older non-Audit Lean files,298 Haskell files\nand207 active package files remain. The306 registries retain1400 entries and five overrides.\nThe final documentary audit is accepted and archived as component20.\nAll nine additive document inverses restore the old bytes. FINDINGS keeps its repair index FIRST.\nThe actual proof ledger remains three passed jobs and zero proof failures.\nThe two root metadata schema failures and both successful corrections remain retained.\nNext-target review is source-only. No next declaration, body or compiler is authorized.\nSupport capture, final seal verification, local publication and authorized root push remain pending.\nCurrent goal turn: PROGRESS. The whole goal stays active. No Haskell repair is added.\n')
print(json.dumps(report))
