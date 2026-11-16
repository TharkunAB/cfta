from pathlib import Path
import datetime
import gzip
import hashlib
import json
import subprocess

root = Path('/home/tritlo/Code/mcfta')
work = Path(__file__).parent
read = lambda *args: subprocess.check_output(['git',*args],cwd=root,text=True).strip()
base = '8154da8fc57ef6e032862467eaac32d82ea7ad5b'
assert read('rev-parse','HEAD') == base and read('branch','--show-current') == 'formalize'
assert not read('diff','--cached','--name-only')
assert not read('diff','--name-only','--','lean/MicroCFTA')
prior = root / 'lean/restart-evidence/20261116-real-callback-and-isolation-checkpoint'
for name,digest in json.loads(gzip.decompress((prior/'source-pins.json.gz').read_bytes())).items():
    assert hashlib.sha256((root/name).read_bytes()).hexdigest() == digest,name
run = root / 'lean/restart-evidence/20261116-native-identity-heap-and-receipt-check'
checks = json.loads((run/'checked.json').read_text())['checks']
assert all(x['exit'] == 0 and not x['nonstandard_axioms'] for x in checks)
assert checks[-1]['total_axiom_reports'] == 81
for name,digest in json.loads((run/'source-pins.json').read_text()).items():
    assert hashlib.sha256((root/name).read_bytes()).hexdigest() == digest,name
packet = root / 'lean/restart-evidence/20261116-current-any-budget-identity-heap-and-receipt-repair'
raw = packet / 'APPEND.lean.txt'
assert hashlib.sha256(raw.read_bytes()).hexdigest() == '176e0086707fc08c6ee06837a41edf959ac55128c6bd1febe22469ddc67e4116'
owner = root/'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'
audit = root/'lean/MicroCFTA/Audit.lean'
(work/'BASE-OWNER.lean.txt').write_bytes(owner.read_bytes())
(work/'BASE-AUDIT.lean.txt').write_bytes(audit.read_bytes())
extra = (packet/'IMPORTS.lean.txt').read_bytes()
assert all(not line.strip() or line.startswith(b'import MicroCFTA.') for line in extra.splitlines())
owner.write_bytes(extra+b'\n'+owner.read_bytes()+b'\n'+raw.read_bytes())
law = 'MicroCFTA.SourcePruningEnumerationSharedEagerReservation.runEager_identity_emitted_resources_at_any_budget'
audit.write_bytes(audit.read_bytes()+('\n#check @'+law+'\n#print axioms '+law+'\n').encode())
subprocess.run(['git','add','--',str(owner.relative_to(root)),'lean/MicroCFTA/Audit.lean'],cwd=root,check=True)
subprocess.run(['git','diff','--cached','--check'],cwd=root,check=True)
subprocess.run(['git','commit','--quiet','-m','Prove identity worker output resources at every supplied budget'],cwd=root,check=True)
proof_commit = read('rev-parse','HEAD')
relocation = root/'lean/restart-evidence/20261116-current-real-callback-owner-relocation-audit'
append = (relocation/'OWNER-APPEND.lean.txt').read_bytes()
assert hashlib.sha256(append).hexdigest() == '2d4fe2d7afbca2f1fc91c21d2b3656a4fd8595d5924909bca25f254b89b00244'
comparisons = json.loads((relocation/'BYTE-COMPARISON.json').read_text())
assert comparisons['public_qnames_unchanged']
assert comparisons['all_three_headers_exact'] and comparisons['all_three_proofs_exact']
for item in comparisons['parts']:
    part = (root/item['part']).read_bytes()
    assert hashlib.sha256(part).hexdigest() == item['sha256']
    assert append.count(part) == 1
names = ['SourcePruningEnumerationRealWorkerCallbackResources','SourcePruningEnumerationRealCapturedCallbackResources']
for name in names:
    target = root/'lean/MicroCFTA'/(name+'.lean')
    (work/(name+'.BEFORE.lean.txt')).write_bytes(target.read_bytes())
    wrapper = (relocation/(name+'.WRAPPER.lean.txt')).read_bytes()
    assert wrapper == b'import MicroCFTA.SourcePruningEnumerationSharedEagerReservation\n'
    target.write_bytes(wrapper)
owner.write_bytes(owner.read_bytes()+b'\n'+append)
subprocess.run(['git','add','--',str(owner.relative_to(root)),*[str((root/'lean/MicroCFTA'/(n+'.lean')).relative_to(root)) for n in names]],cwd=root,check=True)
subprocess.run(['git','diff','--cached','--check'],cwd=root,check=True)
subprocess.run(['git','commit','--quiet','-m','Place recursive callback proofs beside their source task dependencies'],cwd=root,check=True)
(work/'promotion.json').write_text(json.dumps({'at':datetime.datetime.now().astimezone().isoformat(),
    'base':base,'proof_commit':proof_commit,'code':read('rev-parse','HEAD'),'strict_identity_reports':81,
    'original_c831_header_unchanged':True,'callback_headers_proofs_and_public_qnames_byte_exact':True,
    'new_private_exports':False,'new_callback_proof_duplicates':False,'identity_worker_emitted_resources_at_any_budget_proved':True,
    'whole_real_worker_proved':False,'joint_finite_completion_proved':False,'haskell_changed':False},indent=2)+'\n')
print(json.dumps({'proof_commit':proof_commit,'code':read('rev-parse','HEAD')}))
