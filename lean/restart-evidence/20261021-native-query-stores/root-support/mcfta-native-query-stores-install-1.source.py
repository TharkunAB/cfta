import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
PROOF = Path('/tmp/mcfta-native-query-stores-proof')
name = 'SourceCurrentNativeRequestPositivePositions.lean'
target = ROOT / 'lean/MicroCFTA' / name
old = target.read_bytes()
combined = (PROOF / name).read_bytes()
append = (PROOF / 'native-request-call-stores-append.lean.txt').read_bytes()
assert hashlib.sha256(old).hexdigest() == 'e62eed872e07c2457a0ae577e7e35281b48fe4d5ebc6b90bbb403a62e01c5727'
assert hashlib.sha256(combined).hexdigest() == 'e9fe573b314f7e8e4bf65025bb29078165a61a5fa92168f3da65b852b47d4d52'
assert combined.count(b'\n' + append) == 1
assert combined.replace(b'\n' + append, b'', 1) == old
snapshot = HERE / 'native-request-before.lean.txt'
assert not snapshot.exists()
snapshot.write_bytes(old)
target.write_bytes(combined)
adapter = ROOT / 'lean/MicroCFTA/SourceCurrentNativeCurrentStores.lean'
assert not adapter.exists()
data = (PROOF / adapter.name).read_bytes()
assert hashlib.sha256(data).hexdigest() == '48b80476a09c7b4c3f5ce1ef1b35b45cadc6acc6d6f7a401637cadb4f010a728'
adapter.write_bytes(data)
print(json.dumps({'status': 'PASS', 'old_declarations_byte_exact': True,
                  'new_public_theorems': 2, 'added_lines': 108}))
