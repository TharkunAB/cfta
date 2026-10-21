import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
expected = {
    'commit-proofs.py': '9c4a23449cd61d2884b3ada813541b6f13b5d49df370b575c072d79e79b61cd0',
    'verify-checkpoint.py': '6199c5dbeb616e8a6d2dff062925e274d62ed023f4393311f6a36517901ec567',
    'seal-checkpoint.py': 'b3e839954c8572c69d156c33da3f3e7cac5eb3b2f659c25269bbe682b1b1a4b7',
    'verify-seal.py': '66c31c1a9da922463cccc5cb4879a86255157f6b77d6b60d51788ab394ccd8a7',
    'archive-support.py': '5897da734a5577062ed5d994386291a9818a36ecb88d98df8f9bed9890400de4',
    'final-publication.py': '71f96066dfd0c562e652a77aa785d03ee290e74fb18eb61ec6ad8da17b604162',
}
for name, sha in expected.items():
    data = (HERE / 'checkpoint-preparation-v2' / name).read_bytes()
    assert hashlib.sha256(data).hexdigest() == sha
    assert not (HERE / name).exists()
    (HERE / name).write_bytes(data)
print(json.dumps(dict(status='PASS', activated=expected, publication_gate='PENDING_ACTUAL_PROOF_COMMIT')))
