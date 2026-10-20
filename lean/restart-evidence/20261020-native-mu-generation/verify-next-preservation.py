import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
parser = argparse.ArgumentParser()
parser.add_argument('--root', type=Path, default=HERE.parents[2])
args = parser.parse_args()
ROOT = args.root.resolve()


def check(path, item):
    data = path.read_bytes()
    assert len(data) == item['bytes'] and hashlib.sha256(data).hexdigest() == item['sha256'], path


env = {**os.environ, 'PYTHONDONTWRITEBYTECODE': '1'}
prototype = HERE / 'next-stopping-site-prototype'
checked = json.loads(subprocess.check_output([sys.executable, str(prototype / 'stopping-site-verify.py'),
                     '--root', str(ROOT), '--live'], cwd='/', env=env))
assert checked['status'] == 'PASS' and checked['lean_jobs'] == 3 and checked['failed_attempts'] == 1
assert len((prototype / 'SourceCurrentNativeMuStoppingSite.lean').read_text().splitlines()) == 307
draft = HERE / 'next-stopping-generation-draft/SourceCurrentNativeMuStoppingGeneration.lean'
assert hashlib.sha256(draft.read_bytes()).hexdigest() == '7feff34b4826c055d28f020ac9c497afdc46206c84b448a544364c530da9eb90'
assert len(draft.read_text().splitlines()) == 87
for name in ['SourceCurrentNativeMuStoppingSite', 'SourceCurrentNativeMuStoppingGeneration']:
    assert 'import MicroCFTA.' + name + '\n' not in (ROOT / 'lean/MicroCFTA/Audit.lean').read_text()

design = HERE / 'next-blocked-allocation-design'
config = json.loads((design / 'blocked-allocation-design-pins.json').read_text())
for item in config['ROOT']:
    check(ROOT / item['path'], item)
for item in config['HERE']:
    check(design / item['path'], item)
assert config['status'] == 'UNCHECKED_DESIGN' and config['lean_jobs'] == config['checked_heads'] == 0

owner = HERE / 'next-owner-attachment-review'
prefix = 'mcfta-native-optional-owner-attachment-review'
owner_config = json.loads((owner / (prefix + '-source-pins.json')).read_text())
for item in owner_config['files']:
    check(ROOT / item['path'], item)
relocated = {
    '/tmp/mcfta-native-optional-site-fixture/native-site-kernels.lean': HERE / 'native-site-kernels.lean',
    '/tmp/mcfta-native-optional-owner-attachment-review.md': owner / (prefix + '.md'),
}
assert set(relocated) == {item['path'] for item in owner_config['external_files']}
for item in owner_config['external_files']:
    check(relocated[item['path']], item)

print(json.dumps({'status': 'PASS', 'checked_next_prototype_pins': checked['pins'],
                  'next_archived_lean_jobs': 3, 'next_archived_failures': 1,
                  'unchecked_bridge_lines': 87, 'unchecked_blocked_design_pins': len(config['ROOT']) + len(config['HERE']),
                  'owner_design_pins': len(owner_config['files']) + len(owner_config['external_files']),
                  'original_owner_tmp_pins_preserved_with_explicit_archive_mapping': True,
                  'future_components_not_imported_by_current_Audit': True,
                  'new_lean_jobs_for_this_verifier': 0, 'current_public_pairs_added': 0}, indent=2))
