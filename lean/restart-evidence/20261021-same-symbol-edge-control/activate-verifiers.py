import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
expected = {
    'verify-proofs.py': ('proof-verifier-preparation', 'fc062695ef33cffb094499b89a7173c80edb333193e26e35040cdd8276cce84e'),
    'verify-preservation.py': ('preservation-preparation', '5cc572afa76deac05d9cf3492f06ad6d55008e3fa018606d390ac7d0b0caabf5'),
}
for name, (component, sha) in expected.items():
    data = (HERE / component / name).read_bytes()
    assert hashlib.sha256(data).hexdigest() == sha
    assert not (HERE / name).exists()
    (HERE / name).write_bytes(data)
print(json.dumps(dict(status='PASS', activated={name: item[1] for name, item in expected.items()})))
