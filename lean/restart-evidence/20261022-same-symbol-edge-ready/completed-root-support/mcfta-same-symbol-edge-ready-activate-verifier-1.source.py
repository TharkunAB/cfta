import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
data = (HERE / 'proof-verifier-preparation/verify-proofs.py').read_bytes()
sha = hashlib.sha256(data).hexdigest()
assert sha == '45ac9fb2ac0293dbf5841da3a557b08247ad6ba702c605ea6824fbde631ca879'
assert not (HERE / 'verify-proofs.py').exists()
(HERE / 'verify-proofs.py').write_bytes(data)
print(json.dumps({'status': 'PASS', 'activated': 'verify-proofs.py', 'sha256': sha}))
