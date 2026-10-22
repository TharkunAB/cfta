import datetime,hashlib,json,re,subprocess
from pathlib import Path
R=Path('/home/tritlo/Code/mcfta');H=R/'lean/restart-evidence/20261023-original-row-reconstruction';P=Path('/tmp/mcfta-original-row-reconstruction-proposal');A=Path('/tmp/mcfta-original-row-reconstruction-body-audit')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for package,name,expected,count in [(P,'proposal','77a0d9ac6cb148e2ab20e507c707ed9ac6619d47f045331b39b0998023a3eb61',126),(A,'body-audit','ab5e135ef34c596cae265144de766734e3cb1508ee94f6203659a012b249b5c8',131)]:
 assert sha(package/'pins.json')==expected
 pins=json.loads((package/'pins.json').read_text());assert isinstance(pins,list) and len(pins)==count
 for pin in pins:
  p=package/pin['path'];assert p.stat().st_size==pin['bytes'] and sha(p)==pin['sha256'],p
 subprocess.run(['/usr/bin/python3',str(H/'archive-extra.py'),str(package),name],check=True)
source=P/'SourceCurrentOriginalRowReconstruction.lean';data=source.read_bytes()
assert sha(source)=='31f617cdb892cf7eff50ea6f2aa671cb590b94211615e798bddad90538637276' and len(data.splitlines())==210<=350
assert sha(A/'review.md')=='7f409ec32e8b7d95015ac4ffbdd634308560834e2ce8f47207c40756fb5c37c6'
assert json.loads((H/'root-declaration-review.json').read_text())['body_proposal_authorized']
assert json.loads((H/'root-full-tools-review.json').read_text())['status']=='ROOT_ACCEPTED_DECLARATION_BOUND_FULL_TOOLS'
contracts=json.loads((H/'signature-plan/contracts.json').read_text());assert data.startswith((H/'signature-plan/context.lean.txt').read_bytes())
for name in ['private-header.lean.txt','public-header.lean.txt']:
 header=(H/'signature-plan'/name).read_bytes().rstrip(b'\n')+b' := by\n';assert data.count(header)==1
fragments=json.loads((H/'declaration-integration/local-fragment-schema.json').read_text())['fragments']
positions=[]
for fragment in fragments:
 header=fragment['expected_full_type_fragment'].encode();assert data.count(header)==1;positions.append(data.index(header))
assert positions==sorted(positions) and len(fragments)==8
assert not re.search(rb'(?m)^\s*set_option|\bsorry\b|\baxiom\b',data)
report=dict(status='ROOT_ACCEPTED_FOR_FIRST_STRICT',observed_at=datetime.datetime.now().astimezone().isoformat(),source='proposal/SourceCurrentOriginalRowReconstruction.lean',source_sha256=sha(source),source_lines=210,hard_stop=350,shorter_than_target_accepted_without_padding=True,root_read_complete_source=True,independent_complete_source_review='CLEAR',independent_review_sha256=sha(A/'review.md'),exact_context_private_public_and_eight_locals=True,first_strict_authorized=True,official_install_authorized=False,new_proof_jobs=0,whole_goal_complete=False)
(H/'root-source-compile-gate.json').write_text(json.dumps(report,indent=2)+'\n')
with (H/'current-progress.md').open('a') as out:
 out.write('\n## Complete source accepted for first strict\n\nThe complete210-line proposal and independent whole-source review pass.\nIt is below the target range and needs no padding. The350-line hard stop remains.\nAll exact declarations and eight local types match. The initial210-line draft,\ntwo-site uncompiled precaution and packaging diagnostic remain retained.\nRoot authorizes the first strict command. No H23 Lean result or official install is claimed.\n')
print(json.dumps(report))
