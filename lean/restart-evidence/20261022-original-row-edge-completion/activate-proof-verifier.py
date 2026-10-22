import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
data = (HERE / 'proof-verifier-preparation/verify-proofs.py').read_bytes()
sha = hashlib.sha256(data).hexdigest()
assert sha == '706258f300b984349defaf77df761c90a007772b4ab667bc37036bdccc8f955e'
assert not (HERE / 'verify-proofs.py').exists()
(HERE / 'verify-proofs.py').write_bytes(data)
print(json.dumps({'status': 'PASS', 'activated': 'verify-proofs.py', 'sha256': sha}))
