from pathlib import Path
import hashlib
import json
import subprocess

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
work = Path(__file__).parent
packet = base / '20261116-current-any-budget-identity-heap-and-receipt-repair'
raw, probe = packet / 'APPEND.lean.txt', packet / 'ALL-NEW-PROBES.lean.txt'
assert hashlib.sha256(raw.read_bytes()).hexdigest() == '176e0086707fc08c6ee06837a41edf959ac55128c6bd1febe22469ddc67e4116'
assert hashlib.sha256(probe.read_bytes()).hexdigest() == '3e711e444d885b6a016bc575b5910adba0e3e1f3eee6d6dc5c60a2c1afd27ae3'
old = base / '20261115-real-prefix-and-opaque-publication/ResourceProbes.lean.txt'
assert old.read_bytes().count(b'#print axioms ') == 73
(work / 'IDENTITY616-APPEND.lean.txt').write_bytes(raw.read_bytes())
(work / 'Identity61681Probes.lean.txt').write_bytes(old.read_bytes() + b'\n' + probe.read_bytes())
assert (work / 'Identity61681Probes.lean.txt').read_bytes().count(b'#print axioms ') == 81
builder = base / '20261116-real-prefix-all-outcome-checkpoint-work/prepare-consumer-unique.py'
subprocess.run(['python3', str(builder), '--run', '20261116-native-identity-heap-and-receipt-check',
    '--dependency-imports', str(packet / 'IMPORTS.lean.txt'), '--spec',
    work.name + ':IDENTITY616-APPEND.lean.txt:Identity61681Probes.lean.txt'], check=True)
run = base / '20261116-native-identity-heap-and-receipt-check'
pins = json.loads((run / 'source-pins.json').read_text())
for path in [raw,probe,Path(__file__)]:
    pins[str(path.relative_to(root))] = hashlib.sha256(path.read_bytes()).hexdigest()
(run / 'source-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
