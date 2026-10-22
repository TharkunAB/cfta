import datetime,hashlib,json,subprocess
from pathlib import Path
H=Path('/home/tritlo/Code/mcfta/lean/restart-evidence/20261023-original-row-reconstruction');T=Path('/tmp/mcfta-original-row-reconstruction-signature-path-repair');A=Path('/tmp/mcfta-original-row-reconstruction-signature-path-audit')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for package,name,expected,count,kind in [(T,'signature-path-repair','dd9260a1cda7c633adf1a793036c0d6d68cd4f94437cfb1df61b556c3f50a054',10,list),(A,'signature-path-audit','0079fadf94c14e1cf3932c3c46b94ee297ddedbe6b7749cb015bdb58e69985ed',18,dict)]:
 assert sha(package/'pins.json')==expected
 pins=json.loads((package/'pins.json').read_text());assert isinstance(pins,kind) and len(pins)==count
 items=pins if kind is list else [dict(path=name,**pin) for name,pin in pins.items()]
 for pin in items:
  p=package/pin['path'];assert p.stat().st_size==pin['bytes'] and sha(p)==pin['sha256'],p
 subprocess.run(['/usr/bin/python3',str(H/'archive-extra.py'),str(package),name],check=True)
assert sha(A/'review.md')=='ffa36d2d489775af23f796c8518d2ba0a3a24c6a11380ab30b85f4ffb6646bd0'
old=(H/'prepare-selected-full.py').read_text();new=(T/'prepare-selected-full.py').read_text();assert old.count('signature-plan/')==2 and old.replace('signature-plan/','signature-repair/')==new
assert sha(T/'prepare-selected-full.py')=='8c3398646b2f8e982a0cbc17167d06133628d4d23f96f040e1b4019bd831a58c'
assert (H/'declaration-integration/verify-proofs.py').read_text().replace('signature-plan/contracts.json','signature-repair/contracts.json')==(T/'verify-proofs.py').read_text()
(H/'prepare-selected-full.py').write_bytes((T/'prepare-selected-full.py').read_bytes())
(H/'root-full-tools-review.before-signature-path-repair.json').write_bytes((H/'root-full-tools-review.json').read_bytes())
review=json.loads((H/'root-full-tools-review.json').read_text());review.update(observed_at=datetime.datetime.now().astimezone().isoformat(),independent_signature_path_review_sha256=sha(A/'review.md'),signature_path='signature-repair',materializer_sha256=sha(H/'prepare-selected-full.py'))
review['selected_early_full_tools']['prepare-selected-full.py']['sha256']=sha(H/'prepare-selected-full.py')
(H/'root-full-tools-review.json').write_text(json.dumps(review,indent=2)+'\n')
r=json.loads((H/'original-row-reconstruction-strict-2.json').read_text());source=H/r['source'];assert r['exit_code']==0 and not (H/r['log']).read_bytes()
assert sha(source)==r['sha256']=='69ed5b8d01f7bcd1d21aa4a66206c9f0bc9480c728c695bfafd7e8222621e435'
assert source.read_bytes()==(H/'syntax-repair-1/SourceCurrentOriginalRowReconstruction.lean').read_bytes()
selected=H/'selected-sources';assert not selected.exists();selected.mkdir();(selected/'SourceCurrentOriginalRowReconstruction.lean').write_bytes(source.read_bytes())
path='lean/MicroCFTA/SourceCurrentOriginalRowReconstruction.lean'
gate=dict(status='ROOT_ACCEPTED',path=path,sha256=sha(source),lines=210,snapshot='selected-sources/SourceCurrentOriginalRowReconstruction.lean')
(H/'selected-source-gate.json').write_text(json.dumps(gate,indent=2)+'\n')
(H/'selected-sources.json').write_text(json.dumps({path:dict(sha256=sha(source),lines=210,strict='original-row-reconstruction-strict-2',full='original-row-reconstruction-public-1')},indent=2)+'\n')
(H/'frozen-modules.json').write_text(json.dumps({'SourceCurrentOriginalRowReconstruction':sha(source)},indent=2)+'\n')
(H/'root-source-review.json').write_text(json.dumps(dict(status='ROOT_ACCEPTED_CLEAN_STRICT_FOR_FULL',source_sha256=sha(source),source_lines=210,selected_strict='original-row-reconstruction-strict-2',strict_log_literal_empty=True,actual_jobs=2,failed_jobs=1,full_jobs=0,official_install_authorized=False),indent=2)+'\n')
with (H/'current-progress.md').open('a') as out:out.write('\n## Clean strict result selected\n\nStrict2 passes with a literal-empty log on210-line source69ed5b8d.\nThe actual ledger has two source commands and one retained parsing failure.\nRoot and independent path-only tool review pass. Materialization now reads\nthe renewed signature-repair context and header. The selected FULL is pending.\nNo official module installation, Audit or checkpoint publication is claimed.\n')
print(json.dumps(dict(status='PASS',selected_source_sha256=sha(source),strict_log_literal_empty=True,actual_jobs=2,failed_jobs=1,materializer_sha256=sha(H/'prepare-selected-full.py'))))
