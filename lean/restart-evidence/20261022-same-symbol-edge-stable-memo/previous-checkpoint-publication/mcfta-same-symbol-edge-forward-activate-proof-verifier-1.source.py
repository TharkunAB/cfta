import hashlib
from pathlib import Path

HERE = Path(__file__).resolve().parent
data = (HERE / 'proof-verifier-preparation-v2/verify-proofs.py').read_bytes()
assert hashlib.sha256(data).hexdigest() == '717591dbc0de3f279e6ccefbaf978739a7c88a3762c17d377299cb4d4f140a41'
assert not (HERE / 'verify-proofs.py').exists()
(HERE / 'verify-proofs.py').write_bytes(data)
print('Activated exact reviewed 159-line proof verifier.')
