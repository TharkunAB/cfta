import hashlib
from pathlib import Path

HERE = Path(__file__).resolve().parent
source = (HERE / 'proof-verifier-preparation/verify-proofs.py').read_bytes()
assert hashlib.sha256(source).hexdigest() == 'f92513d3afb9bd2eeb39a715ef19b53a8fd3ffa803bc9981228e1ba46ddd7daf'
assert not (HERE / 'verify-proofs.py').exists()
(HERE / 'verify-proofs.py').write_bytes(source)
print('Activated the exact reviewed saved-evidence verifier.')
