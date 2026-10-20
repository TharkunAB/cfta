import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def check(path, entry):
    data = path.read_bytes()
    assert len(data) == entry['bytes'], str(path)
    assert hashlib.sha256(data).hexdigest() == entry['sha256'], str(path)


pins = json.loads((HERE / 'source-review.source-pins.json').read_text())
check(HERE / 'source-review.md', pins['review'])
for entry in pins['files']:
    check(ROOT / entry['path'], entry)
assert len(pins['candidate_files']) == 1
entry = pins['candidate_files'][0]
assert entry['path'] == 'SourceCurrentNativeOriginalUnionDescent.lean'
check(ROOT / 'lean/MicroCFTA' / entry['path'], entry)
assert all(value == 0 for value in pins['counts'].values())
result = subprocess.check_output([
    sys.executable, str(HERE / 'fixture-review/mcfta-native-union-fixture-review-verify.py'),
    '--live', '--root', str(ROOT), '--fixture', str(HERE / 'union-fixture'),
], cwd='/', env={**os.environ, 'PYTHONDONTWRITEBYTECODE': '1'})
review = json.loads(result)
assert review['status'] == 'PASS'
repair = json.loads((HERE / 'upstream-binders-size-order.json').read_text())
assert repair['commit'] == '7469183231da3a9c7aefc115c9cc818f4867bd9d'
patch = subprocess.check_output([
    'git', 'show', '--format=fuller', repair['commit'], '--',
    'cfta-generator/src/Data/CFTA/Gen/Typing.hs', 'cfta-generator/README.md', 'cfta-generator/CHANGELOG.md',
], cwd=ROOT)
assert patch == (HERE / 'upstream-binders-size-order-7469183.patch').read_bytes()
assert repair['production_haskell_changes'] is False
print(json.dumps({'status': 'PASS', 'source_reviews': 1,
                  'source_review_pins': 2 + len(pins['files']),
                  'fixture_review': review, 'external_documentation_patch_matches_commit': True,
                  'new_lean_jobs': 0, 'new_pairs': 0}))
