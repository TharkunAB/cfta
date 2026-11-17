from pathlib import Path
import datetime
import hashlib
import json
import subprocess

ROOT = Path('/home/tritlo/Code/mcfta')
WORK = Path(__file__).resolve().parent
GIT = lambda *args: subprocess.check_output(['git', *args], cwd=ROOT)
prior = 'a59893a37d6c30b25a92f6ac499e5115057b9383'
stage = json.loads((WORK / 'SOURCES-NORMAL-STAGING.json').read_text())
verified = json.loads((WORK / 'PUBLICATION-VERIFIED.json').read_text())
assert verified['actual_terminal'] and verified['actual_terminal_exit'] == 0
assert len(verified['checks']) == 5 and all(c['exit'] == 0 and not c['diagnostics']
    and not c['sorryAx'] and not c['nonstandard_axioms'] for c in verified['checks'])
assert GIT('branch', '--show-current').decode().strip() == 'formalize'
assert GIT('rev-parse', 'HEAD').decode().strip() == prior
assert not GIT('diff', '--cached', '--name-only')
files = [item['source_path'] for item in stage['components']] + ['lean/MicroCFTA/Audit.lean']
assert len(files) == len(set(files)) == 4
for item in stage['components']:
    assert hashlib.sha256((ROOT / item['source_path']).read_bytes()).hexdigest() == item['raw_sha256']
assert GIT('diff', '--name-only').decode().splitlines() == ['lean/MicroCFTA/Audit.lean']
assert not (WORK / 'SOURCE-COMMIT.json').exists()
subprocess.run(['git', 'add', '-f', '--', *files], check=True, cwd=ROOT)
assert set(GIT('diff', '--cached', '--name-only').decode().splitlines()) == set(files)
subprocess.run(['git', 'diff', '--cached', '--check'], check=True, cwd=ROOT)
subprocess.run(['git', 'commit', '--quiet', '-m',
    'Preserve Mu inventory through the next warm query and every bounded prefix'], check=True, cwd=ROOT)
head = GIT('rev-parse', 'HEAD').decode().strip()
assert GIT('rev-parse', head + '^').decode().strip() == prior
assert not GIT('status', '--porcelain', '--untracked-files=no')
receipt = {'at': datetime.datetime.now().astimezone().isoformat(), 'source_commit': head,
    'parent': prior, 'files': files, 'actual_terminal': True, 'actual_terminal_exit': 0,
    'joint_finite_completion_proved': False, 'haskell_changed': False}
(WORK / 'SOURCE-COMMIT.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt))
