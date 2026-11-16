from pathlib import Path
import datetime
import hashlib
import json
import subprocess

root = Path('/home/tritlo/Code/mcfta')
work = Path(__file__).parent
read = lambda *args: subprocess.check_output(['git', *args], cwd=root).decode().strip()
assert read('rev-parse','HEAD') == 'f9cfbd5169474d14e0b56b45f5aa8e40299169ec'
assert read('branch','--show-current') == 'formalize'
assert not read('diff','--cached','--name-only')
assert not read('diff','--name-only','--','lean/MicroCFTA')
run = root / 'lean/restart-evidence/20261116-native-prefix-native-readback-bool-check'
checked = json.loads((run / 'checked.json').read_text())
assert all(item['exit'] == 0 and not item['nonstandard_axioms'] for item in checked['checks'])
assert checked['checks'][-1]['total_axiom_reports'] == 1
for name,digest in json.loads((run / 'source-pins.json').read_text()).items():
    assert hashlib.sha256((root / name).read_bytes()).hexdigest() == digest, name
raw = root / 'lean/restart-evidence/20261116-current-real-prefix-native-readback-bool-repair/SourcePruningEnumerationPrefixNativeReadback.lean'
assert hashlib.sha256(raw.read_bytes()).hexdigest() == '34cd7a9b3713ee545d4db4f0fa5de960e1b7da6aaf9aad01f491fddd35a0e66f'
target = root / 'lean/MicroCFTA' / raw.name
assert not target.exists()
target.write_bytes(raw.read_bytes())
audit = root / 'lean/MicroCFTA/Audit.lean'
law = 'MicroCFTA.SourcePruningEnumerationSelectedStep.prefix_native_readback_at_original_budget'
assert ('theorem '+law.rsplit('.',1)[1]) in raw.read_text()
audit.write_bytes(('import MicroCFTA.'+target.stem+'\n').encode()+audit.read_bytes()+('\n#check @'+law+'\n#print axioms '+law+'\n').encode())
subprocess.run(['git','add','--',str(target.relative_to(root)),'lean/MicroCFTA/Audit.lean'],cwd=root,check=True)
subprocess.run(['git','diff','--cached','--check'],cwd=root,check=True)
subprocess.run(['git','commit','--quiet','-m','Preserve native readback through every actual prefix outcome'],cwd=root,check=True)
(work / 'readback-promotion.json').write_text(json.dumps({'at':datetime.datetime.now().astimezone().isoformat(),
    'code':read('rev-parse','HEAD'),'new_public_theorems':1,'source_files':6126,
    'whole_real_worker_proved':False,'joint_finite_completion_proved':False,'haskell_changed':False},indent=2)+'\n')
print(read('rev-parse','HEAD'))
