import datetime,hashlib,json,subprocess
from pathlib import Path
R=Path('/home/tritlo/Code/mcfta');H=R/'lean/restart-evidence/20261023-original-row-reconstruction';P=Path('/tmp/mcfta-original-row-reconstruction-repair-1');A=Path('/tmp/mcfta-original-row-reconstruction-repair-1-audit')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for package,name,expected,count in [(P,'syntax-repair-1','1ff693e8ef12e5eb4cebbfebf3656dd7d9034ebfc200ba34e8b853db947910cd',119),(A,'syntax-repair-1-audit','a00094621b57e01ddb512744671497c4d0c897643ae119a5338e7934fe56bf23',124)]:
 assert sha(package/'pins.json')==expected
 pins=json.loads((package/'pins.json').read_text());assert isinstance(pins,list) and len(pins)==count
 for pin in pins:
  p=package/pin['path'];assert p.stat().st_size==pin['bytes'] and sha(p)==pin['sha256'],p
 subprocess.run(['/usr/bin/python3',str(H/'archive-extra.py'),str(package),name],check=True)
subprocess.run(['/usr/bin/python3',str(H/'archive-extra.py'),str(P/'signature-repair'),'signature-repair'],check=True)
source=P/'SourceCurrentOriginalRowReconstruction.lean';assert sha(source)=='69ed5b8d01f7bcd1d21aa4a66206c9f0bc9480c728c695bfafd7e8222621e435' and len(source.read_bytes().splitlines())==210
assert sha(A/'review.md')=='7214c00ae8be635a487e01105cc2a88e537a24c7007f75e08af03777a1ee70a8'
assert sha(H/'signature-repair/contracts.json')=='63d356619295a39168f5bc4011bfbabb6df6666784ee476fc0313582973f6a4f'
contracts=json.loads((H/'signature-repair/contracts.json').read_text())
for name,pin in contracts.items():
 p=H/'signature-repair'/name;assert sha(p)==pin['sha256'] and len(p.read_bytes().splitlines())==pin['lines']
for name in ['context.lean.txt','local-statements.lean.txt']:assert (H/'signature-repair'/name).read_bytes()==(H/'signature-plan'/name).read_bytes()
previous=H/'root-declaration-review.before-syntax-repair.json';assert not previous.exists();previous.write_bytes((H/'root-declaration-review.json').read_bytes())
review=json.loads(previous.read_text());assert review['contract_sha256']=='c2202a31a91d7df7b2440a88bd3c2654f7929d7d2d668635c02fc501625d5f04'
review.update(observed_at=datetime.datetime.now().astimezone().isoformat(),contract_sha256=sha(H/'signature-repair/contracts.json'),contracts=[dict(path=name,lines=pin['lines'],sha256=pin['sha256']) for name,pin in contracts.items()],independent_review_sha256=sha(A/'review.md'),renewal='Three application parentheses pairs after actual failed strict1; all premises/conclusions and eight local types retain the same intended contract.',previous_review_preserved=str(previous.relative_to(H)))
(H/'root-declaration-review.json').write_text(json.dumps(review,indent=2)+'\n')
report=dict(status='ROOT_ACCEPTED_SYNTAX_REPAIR_FOR_NEXT_STRICT',observed_at=datetime.datetime.now().astimezone().isoformat(),source='syntax-repair-1/SourceCurrentOriginalRowReconstruction.lean',source_sha256=sha(source),source_lines=210,root_read_complete_source=True,independent_complete_source_review='CLEAR',independent_review_sha256=sha(A/'review.md'),renewed_contract_sha256=review['contract_sha256'],retained_actual_failed_jobs=1,retained_actual_source_errors=2,next_strict_authorized=True,official_install_authorized=False,full_materializer_path_repair_still_requires_tool_audit=True)
(H/'root-source-compile-gate-repair-1.json').write_text(json.dumps(report,indent=2)+'\n')
with (H/'current-progress.md').open('a') as out:out.write('\n## Reviewed syntax repair\n\nRoot and independent whole-source reviews pass for210-line repair69ed5b8d.\nOnly three application parentheses pairs change. The renewed exact declarations\nare archived separately under signature-repair; original signature-plan remains immutable.\nThe eight local types and all semantic premises/conclusions retain the same intended contract.\nRoot authorizes strict2. The failed strict1 remains in the actual ledger.\nThe separate tool-path review is still required before materialization.\nNo FULL, Audit or official installation is claimed.\n')
print(json.dumps(report))
