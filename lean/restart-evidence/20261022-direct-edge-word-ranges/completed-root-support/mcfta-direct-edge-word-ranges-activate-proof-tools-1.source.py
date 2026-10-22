import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
assert (HERE / 'actual-binding-audit/review.md').is_file()
expected = {
    'verify-preservation.py': 'c7735a6de3c5f2ea811e050fd5f47628fa0c498fcf537c25c0c98f8f2cfbfa77',
    'verify-checkpoint.py': '0e4fef18c8a010571d00f8e2639a4ddf2a5af0bce2d486c7fa431fb00ffcea3a',
    'commit-proofs.py': '7154c6bd94fd9084d9d95f4af3744b72f1058da9c4f6e03cdd32f2aacd261b92',
    'seal-checkpoint.py': '886c2211d58e2cc1c4428d17a4149c25817349fb0b64f200a0706eedd4827c67',
    'verify-seal.py': '66c31c1a9da922463cccc5cb4879a86255157f6b77d6b60d51788ab394ccd8a7',
    'archive-support.py': '9a1a73dcd31748578c3d6d2388e415655c05e3f7d783c39c8d5f98df5d496951',
    'final-publication.py': '2ed5a6d77c61782f76db2c93d167fd6c310a3ad1eb391aecb7928e6245d3fc11',
    'update-documents.py': 'bb16bbb47329cb0a444072d09523e47a9a2ba184f26bbcc37ab738f01fec1b65',
    'verify-proofs.py': 'a94e811c4e781adb059db37068d5290bcdae3dc689633469af73b12d49c7ca38',
}
for name, sha in expected.items():
    directory = 'actual-verifier-preparation' if name == 'verify-proofs.py' else 'actual-tools-preparation'
    data = (HERE / directory / name).read_bytes()
    assert hashlib.sha256(data).hexdigest() == sha
    assert not (HERE / name).exists()
    (HERE / name).write_bytes(data)
print(json.dumps({'status': 'PASS', 'activated': expected, 'network_publication': 'PENDING_USER_APPROVAL'}))
