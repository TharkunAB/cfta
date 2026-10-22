import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
expected = {
    'verify-preservation.py': 'aa635eeec378629deecaf03f6cd02a38edce38a3fbabf36e879a66fe538c0268',
    'verify-checkpoint.py': 'ff2c434be8a95709f21c7d0f83c22208dfd49d54577ce6bf509015f95a4eb5fb',
    'commit-proofs.py': 'cc7d31174023c4797d061278285a1a696f5ac8f959bfb27048b948047c79bd65',
    'seal-checkpoint.py': '79194f3cfbf9682b3c7e0ed8ac5968df665e32e4229f0e0a77465c2b52513af0',
    'verify-seal.py': '66c31c1a9da922463cccc5cb4879a86255157f6b77d6b60d51788ab394ccd8a7',
    'archive-support.py': 'f0ceedb8ee0f23c0c0a621b2daefdad36c8e8d5294d58c800187ae37a8d478e6',
    'final-publication.py': 'aedf9cf3971b9f0f9478f1b38c2b1b02fd20ec76c534d0bab52dff2d540216b9',
    'update-documents.py': 'fc4d3314ba2c984e28553256570689393a2598847ae1f77368ae35d41fe7e7cf',
}
for name, sha in expected.items():
    data = (HERE / 'actual-tools-preparation' / name).read_bytes()
    assert hashlib.sha256(data).hexdigest() == sha
    assert not (HERE / name).exists()
    (HERE / name).write_bytes(data)
print(json.dumps({'status': 'PASS', 'activated': expected, 'publication': 'PENDING_ACTUAL_PROOF_COMMIT_GATE'}))
