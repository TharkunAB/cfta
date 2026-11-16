from pathlib import Path
import datetime
import hashlib
import json
import subprocess

root = Path('/home/tritlo/Code/mcfta')
work = Path(__file__).parent
read = lambda *args: subprocess.check_output(['git', *args], cwd=root).decode().strip()
assert read('rev-parse','HEAD') == '231b8074576aa9e8113c2d7494214b9f5893ada9'
assert read('branch','--show-current') == 'formalize'
assert not read('diff','--cached','--name-only')
assert not read('diff','--name-only','--','lean/MicroCFTA')
run = root / 'lean/restart-evidence/20261116-native-real-captured-callback-check'
checked = json.loads((run / 'checked.json').read_text())
assert all(item['exit'] == 0 and not item['nonstandard_axioms'] for item in checked['checks'])
assert checked['checks'][-1]['total_axiom_reports'] == 1
for name,digest in json.loads((run / 'source-pins.json').read_text()).items():
    assert hashlib.sha256((root / name).read_bytes()).hexdigest() == digest, name
raw = root / 'lean/restart-evidence/20261116-current-real-captured-callback-transport-draft/SourcePruningEnumerationRealCapturedCallbackResources.lean'
assert hashlib.sha256(raw.read_bytes()).hexdigest() == '3b3bb8f8ef2d966cdf37cb05de2f326c3fed7593602576f0935ee52874ab38e7'
target = root / 'lean/MicroCFTA' / raw.name
assert not target.exists()
target.write_bytes(raw.read_bytes())
audit = root / 'lean/MicroCFTA/Audit.lean'
law = 'MicroCFTA.SourcePruningEnumerationRealCapturedCallbackResources.completed_real_callback_captured_packet_at_original_budget'
assert ('theorem '+law.rsplit('.',1)[1]) in raw.read_text()
audit.write_bytes(('import MicroCFTA.'+target.stem+'\n').encode()+audit.read_bytes()+('\n#check @'+law+'\n#print axioms '+law+'\n').encode())
subprocess.run(['git','add','--',str(target.relative_to(root)),'lean/MicroCFTA/Audit.lean'],cwd=root,check=True)
subprocess.run(['git','diff','--cached','--check'],cwd=root,check=True)
subprocess.run(['git','commit','--quiet','-m','Preserve captured input resources after actual recursive callbacks'],cwd=root,check=True)
(work / 'captured-promotion.json').write_text(json.dumps({'at':datetime.datetime.now().astimezone().isoformat(),
    'code':read('rev-parse','HEAD'),'new_public_theorems':1,'source_files':6124,
    'whole_real_worker_proved':False,'joint_finite_completion_proved':False,'haskell_changed':False},indent=2)+'\n')
print(read('rev-parse','HEAD'))
