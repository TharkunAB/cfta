import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
review = json.loads((HERE / 'root-checkpoint-tools-review.json').read_text())
assert review['root_whole_source_and_delta_review'] == 'CLEAR'
assert review['independent_final_source_and_pin_review'] == 'CLEAR'
assert review['activation_authorized'] is True
assert hashlib.sha256((HERE / 'checkpoint-tools-v2-audit/review.md').read_bytes()).hexdigest() == review['independent_review_sha256']
pins = {
    'verify-checkpoint.py': 'b54ddfdb6c3e05fcbb67bcb989120892636fac3f8f9c15ba7ac55f95614d1b95',
    'seal-checkpoint.py': '3798cca17487ae285c932ba032b94ae54f3f4d52a2835f3f8aca2f82f50a263f',
    'verify-seal.py': '66c31c1a9da922463cccc5cb4879a86255157f6b77d6b60d51788ab394ccd8a7',
    'archive-support.py': '051e1b890240a2e481e49d63db2ffbadda102698df679e15393040dad92daeca',
    'final-publication.py': '748949d629c4c183b0695f2c33d8a49743582756755ce7ffddfb16e6e35fe4e3'}
for name, expected in pins.items():
    assert not (HERE / name).exists()
    assert hashlib.sha256((HERE / 'checkpoint-tools-preparation-v2' / name).read_bytes()).hexdigest() == expected
for name in pins:
    (HERE / name).write_bytes((HERE / 'checkpoint-tools-preparation-v2' / name).read_bytes())
print(json.dumps({'status': 'PASS', 'activated_scripts': pins, 'publisher_proof_pin_pending': True}))
