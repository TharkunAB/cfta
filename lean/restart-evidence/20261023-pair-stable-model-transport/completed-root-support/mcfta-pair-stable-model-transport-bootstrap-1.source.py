import datetime
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
previous = root / 'lean/restart-evidence/20261023-original-row-reconstruction'
here = root / 'lean/restart-evidence/20261023-pair-stable-model-transport'
start = '0d03a28e82f9f3d0b5dfbba16bc919fb16c422cb'
digest = lambda data: hashlib.sha256(data).hexdigest()
def git(*args):
    return subprocess.check_output(['git', *args], cwd=root)

assert git('rev-parse', 'HEAD').decode().strip() == start
assert git('branch', '--show-current').decode().strip() == 'formalize'
assert not git('status', '--porcelain')
pull_receipt = Path('/tmp/mcfta-pair-stable-model-transport-initial-pull-2.json')
assert json.loads(pull_receipt.read_bytes())['exit_code'] == 0
push_path = Path('/tmp/mcfta-original-row-reconstruction-authorized-push.json')
push = json.loads(push_path.read_bytes())
assert push['status'] == 'PUSHED_AND_REMOTE_VERIFIED' and push['checkpoint'] == start
assert not here.exists()
here.mkdir()
backup = 'codex/backup-pair-stable-model-transport-' + datetime.datetime.now().astimezone().strftime('%Y%m%d-%H%M')
subprocess.run(['git', 'branch', backup, start], cwd=root, check=True)
(here / 'backup-ref.txt').write_text(backup + '\n')
baseline = {}
for raw in git('ls-tree', '-r', '-z', start).split(b'\0'):
    if not raw:
        continue
    meta, name = raw.split(b'\t', 1)
    mode, kind, blob = meta.decode().split()
    assert kind == 'blob'
    name = name.decode()
    path = root / name
    data = path.read_bytes()
    assert ('100755' if path.stat().st_mode & 0o111 else '100644') == mode, name
    assert hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest() == blob, name
    baseline[name] = dict(mode=mode, blob=blob, sha256=digest(data))
assert len(baseline) == 100056
(here / 'starting-files.json').write_text(json.dumps(baseline, indent=2) + '\n')
for name, arguments in {
    'starting-head.txt': ('rev-parse', 'HEAD'), 'starting-main.txt': ('rev-parse', 'origin/main'),
    'starting-local-main.txt': ('rev-parse', 'main'), 'starting-stashes.txt': ('stash', 'list', '--format=%gd %H %s'),
    'starting-worktrees.txt': ('worktree', 'list', '--porcelain')}.items():
    (here / name).write_bytes(git(*arguments))
(here / 'initial-pull-receipt.json').write_bytes(pull_receipt.read_bytes())
(here / 'pull.log').write_bytes(Path('/tmp/mcfta-pair-stable-model-transport-initial-pull-https.log').read_bytes())
pull_history = here / 'initial-pull-attempts'
pull_history.mkdir()
for stem in ['initial-pull-1', 'initial-pull-2']:
    for suffix in ['.json', '.log', '.limits.json', '.peaks.txt', '.source.py', '.usage.json']:
        path = Path('/tmp/mcfta-pair-stable-model-transport-' + stem + suffix)
        shutil.copyfile(path, pull_history / path.name)
for name in ['initial-pull.log', 'initial-pull-https.log']:
    path = Path('/tmp/mcfta-pair-stable-model-transport-' + name)
    shutil.copyfile(path, pull_history / path.name)
audit = (root / 'lean/MicroCFTA/Audit.lean').read_bytes()
(here / 'original-sources').mkdir()
(here / 'original-sources/Audit.original.lean.txt').write_bytes(audit)
(here / 'original-source-index.json').write_text(json.dumps(dict(sources=[dict(path='lean/MicroCFTA/Audit.lean',
    snapshot='original-sources/Audit.original.lean.txt', lines=len(audit.splitlines()), sha256=digest(audit))]), indent=2) + '\n')
for name in ['root-capped-worker.py', 'archive-extra.py', 'haskell-repair-index.md']:
    (here / name).write_bytes((previous / name).read_bytes())
old_driver = Path('/tmp/mcfta-original-row-reconstruction-driver.py').read_text()
assert old_driver.count('20261023-original-row-reconstruction') == 1
driver = old_driver.replace('20261023-original-row-reconstruction', '20261023-pair-stable-model-transport')
(here / 'root-driver.py').write_text(driver)
Path('/tmp/mcfta-pair-stable-model-transport-driver.py').write_text(driver)
target = here / 'previous-local-checkpoint'
target.mkdir()
retained = {}
names = [Path('/tmp/mcfta-original-row-reconstruction-local-publication.json'), push_path]
for stem in ['support-1', 'seal-1', 'local-publication-1', 'authorized-push-1']:
    prefix = 'mcfta-original-row-reconstruction-' + stem
    for suffix in ['.json', '.log', '.limits.json', '.peaks.txt', '.source.py', '.usage.json']:
        names.append(Path('/tmp') / (prefix + suffix))
for path in names:
    data = path.read_bytes()
    shutil.copyfile(path, target / path.name)
    retained[path.name] = digest(data)
pull_retained = {path.name: digest(path.read_bytes()) for path in pull_history.iterdir()}
assert len(pull_retained) == 14
(here / 'archived-components.json').write_text(json.dumps({'previous-local-checkpoint': retained,
    'initial-pull-attempts': pull_retained}, indent=2) + '\n')
(here / 'previous-local-checkpoint.json').write_bytes(names[0].read_bytes())
(here / 'previous-authorized-push.json').write_bytes(push_path.read_bytes())
counts = dict(status='PASS', baseline_files=len(baseline),
    older_non_audit_lean=sum(name.startswith('lean/MicroCFTA/') and name.endswith('.lean')
        and name != 'lean/MicroCFTA/Audit.lean' for name in baseline),
    haskell_files=sum(name.endswith('.hs') for name in baseline),
    active_package_files=sum(name.split('/')[0] in {'cfta', 'cfta-generator', 'cfta-ghc', 'decision-model'} for name in baseline),
    original_audit_lines=len(audit.splitlines()), original_audit_sha256=digest(audit),
    initial_pull_attempts=2, failed_initial_pull_attempts=1, proof_jobs=0,
    starting_head=start, backup=backup, observed_at=datetime.datetime.now().astimezone().isoformat())
assert (counts['older_non_audit_lean'], counts['haskell_files'], counts['active_package_files']) == (3639, 298, 207)
(here / 'baseline-counts.json').write_text(json.dumps(counts, indent=2) + '\n')
(here / 'current-progress.md').write_text('''# Populated wrapper model transport

The whole formalization goal remains ACTIVE. The preceding goal turn made progress.
H23 proved ordinary original-row reconstruction and pushed both verified commits.
Its remote checkpoint is0d03a28e82f9f3d0b5dfbba16bc919fb16c422cb.
The fresh fast-forward pull and exact file/mode baseline pass.
The first SSH fetch timed out. The HTTPS-only retry passed. Both attempts remain.
The next component transports Stable for the same populated Wrapper under finite input Agreement.
Old captured canonical-request EdgeInputs remain explicit. No new result-law premise is allowed.
Native all-phase Covered, actual publication admission, generated-root composition,
new-source resource certificates, Mu/public-pass behavior and Haskell refinement remain open.
No new declaration, proof body, compiler or prepared evidence tool is authorized yet.
H6 remains strongest combined. FINDINGS keeps the Haskell repair index FIRST.
No Haskell repair is added. No board operation or memory update is authorized.
''')
print(json.dumps(counts))
