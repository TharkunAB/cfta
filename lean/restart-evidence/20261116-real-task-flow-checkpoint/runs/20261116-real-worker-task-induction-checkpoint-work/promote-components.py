from pathlib import Path
import hashlib
import json
import subprocess

root=Path('/home/tritlo/Code/mcfta')
base=root/'lean/restart-evidence'
work=Path(__file__).parent
owner=root/'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'
audit=root/'lean/MicroCFTA/Audit.lean'
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()=='10a69e8c44e5efdf6c982677442a71276ff3e60d'
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=root,text=True)
checks=json.loads((base/'20261116-native-real-fallback-forecast-and-payload-check/checks.json').read_text())
assert len(checks)==3 and all(x['exit']==0 and not x['nonstandard_axioms'] for x in checks)
old_owner=owner.read_bytes();old_audit=audit.read_bytes()
(work/'BASE-OWNER.lean.txt').write_bytes(old_owner)
(work/'BASE-AUDIT.lean.txt').write_bytes(old_audit)
components=[
 ('20261116-current-real-actual-source-tuple-nil-instance-and-configuration-repair','f44ba62cc3859b5b48bef5dab76dbc59931ce93c01efd353494bf76954acafdf','Prove real tuple completion resources from genuine induction'),
 ('20261116-current-real-actual-source-tuple-cons-resources-draft','7bda5a53b542077f7a2f3cfe173d2c01fcff3dd65aa5b04e24a3f147edaea9e4','Prove real tuple continuation resources at original budget'),
 ('20261116-current-real-fallback-forecast-reduction-repair','7e4b143ea815b79e3dbc6b239915f93e7f441722fa5271cf2c0f6826469e4ffa','Prove real fallback resources from actual dispatch receipts')]
commits=[]
for folder,digest,message in components:
    data=(base/folder/'APPEND.lean.txt').read_bytes()
    assert hashlib.sha256(data).hexdigest()==digest
    before=owner.read_bytes();owner.write_bytes(before+b'\n'+data)
    assert owner.read_bytes().startswith(before)
    subprocess.run(['git','diff','--check'],cwd=root,check=True)
    subprocess.run(['git','add',str(owner.relative_to(root))],cwd=root,check=True)
    subprocess.run(['git','commit','--quiet','-m',message],cwd=root,check=True)
    commits.append(subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip())
packet=base/'20261116-current-past-entry-inner-payload-transport-draft'
name='SourceCurrentAllocatedNativePastEntryInnerPayloadTransport.lean'
data=(packet/name).read_bytes()
assert hashlib.sha256(data).hexdigest()=='5a156dcc4db43f5a2ad58b626a88214c2f480872a8b14c2e5817155692bd278f'
target=root/'lean/MicroCFTA'/name;assert not target.exists();target.write_bytes(data)
module='MicroCFTA.'+name[:-5]
probe=(packet/'PROBES.lean.txt').read_bytes()
assert probe.count(b'#print axioms ')==1
audit.write_bytes(('import '+module+'\n').encode()+old_audit+b'\n'+probe)
assert old_audit in audit.read_bytes()
subprocess.run(['git','diff','--check'],cwd=root,check=True)
subprocess.run(['git','add',str(target.relative_to(root)),str(audit.relative_to(root))],cwd=root,check=True)
subprocess.run(['git','commit','--quiet','-m','Transport authentic past payload laws across equal domain keys'],cwd=root,check=True)
commits.append(subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip())
(work/'promotion.json').write_text(json.dumps({'commits':commits,'checked_private_session':25491,
    'owner_probes':105,'payload_reports':1,'old_owner_and_audit_bytes_preserved_as_exact_blocks':True,
    'full_real_worker_proved':False,'joint_finite_completion_proved':False,'haskell_changed':False},indent=2)+'\n')
print(json.dumps({'commits':commits,'head':commits[-1]}))
