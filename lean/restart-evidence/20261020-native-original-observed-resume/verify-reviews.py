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
mapped = {
    'SourceCurrentNativeOriginalObservedResume.lean': ROOT / 'lean/MicroCFTA/SourceCurrentNativeOriginalObservedResume.lean',
    'binder-kernels.lean': ROOT / 'lean/restart-evidence/20261020-native-original-binder-resume/binder-fixture/binder-kernels.lean',
}
assert {entry['path'] for entry in pins['candidate_and_fixture_files']} == set(mapped)
for entry in pins['candidate_and_fixture_files']:
    check(mapped[entry['path']], entry)
assert pins['counts'] == dict(new_jobs=0, owned_pairs=0, reused_pairs=0, new_fixtures_reviewed=0)
result = subprocess.check_output([
    sys.executable, str(HERE / 'fixture-review/mcfta-native-observed-resume-fixture-review-verify.py'),
    '--live', '--root', str(ROOT), '--fixture', str(HERE / 'observed-fixture'),
], cwd='/', env={**os.environ, 'PYTHONDONTWRITEBYTECODE': '1'})
review = json.loads(result)
assert review['status'] == 'PASS'
print(json.dumps({'status': 'PASS', 'source_reviews': 1,
                  'source_review_pins': 1 + len(pins['files']) + len(mapped),
                  'fixture_review': review, 'new_lean_jobs': 0, 'new_pairs': 0}))
