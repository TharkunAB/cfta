import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
expected = {
    'verify-preservation.py': 'bfa559d6ea3a2e1faf309a182f5f66644e694ae1fc52c2beea707e19e1c40ba2',
    'verify-checkpoint.py': '419c6e50135432f88f9981a9ed15865696d7b86db408548f8413e765a67688ce',
    'commit-proofs.py': 'dcc1f8a0a2534f9f913159b9a2ffd67adf893a25b0d8e363a99e4693ff349a8f',
    'seal-checkpoint.py': '663a0d7beb6fcde79efbb65a3621598f8ff72cfb124d9504bebb53935487026e',
    'verify-seal.py': '66c31c1a9da922463cccc5cb4879a86255157f6b77d6b60d51788ab394ccd8a7',
    'archive-support.py': 'eefc7ecf12637e279de196635a8ecb77e331c4768dc6409e4d045a6dd72cc31c',
    'final-publication.py': '98421264ae1579a81032fe0b88f9b33b49db6ada12f28cef8e8dec72cde75262',
    'update-documents.py': '47c834b5fbb82e6f2e5d44a0b55de3a5a1d7c163651cf56747a6a3d8897f0456',
}
for name, sha in expected.items():
    data = (HERE / 'actual-tools-preparation' / name).read_bytes()
    assert hashlib.sha256(data).hexdigest() == sha
    assert not (HERE / name).exists()
    (HERE / name).write_bytes(data)
print(json.dumps({'status': 'PASS', 'activated': expected, 'publication': 'PENDING_ACTUAL_PROOF_COMMIT_GATE'}))
