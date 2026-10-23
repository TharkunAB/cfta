import datetime
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

ROOT = Path('/home/tritlo/Code/mcfta')
PREVIOUS = ROOT / 'lean/restart-evidence/20261023-pair-request-admission'
HERE = ROOT / 'lean/restart-evidence/20261023-both-miss-native-covered'
START = '6ca7ff763c6e18d69904b4e860c11f7959eb3d13'
NAME = 'mcfta-both-miss-native-covered'
def digest(data):
    return hashlib.sha256(data).hexdigest()
def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)

assert git('rev-parse', 'HEAD').decode().strip() == START
assert git('branch', '--show-current').decode().strip() == 'formalize'
assert not git('status', '--porcelain')
pull = Path('/tmp/' + NAME + '-initial-pull-1.json')
assert json.loads(pull.read_bytes())['exit_code'] == 0
push_path = Path('/tmp/mcfta-pair-request-admission-authorized-push.json')
push = json.loads(push_path.read_bytes())
assert push['status'] == 'PUSHED_AND_REMOTE_VERIFIED' and push['checkpoint'] == START
assert not HERE.exists()
HERE.mkdir()
backup = 'codex/backup-both-miss-native-covered-' + datetime.datetime.now().astimezone().strftime('%Y%m%d-%H%M')
subprocess.run(['git', 'branch', backup, START], cwd=ROOT, check=True)
(HERE / 'backup-ref.txt').write_text(backup + '\n')
baseline = {}
for raw in git('ls-tree', '-r', '-z', START).split(b'\0'):
    if not raw:
        continue
    meta, name = raw.split(b'\t', 1)
    mode, kind, blob = meta.decode().split()
    assert kind == 'blob'
    name = name.decode()
    path = ROOT / name
    data = path.read_bytes()
    assert ('100755' if path.stat().st_mode & 0o111 else '100644') == mode, name
    assert hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest() == blob, name
    baseline[name] = dict(mode=mode, blob=blob, sha256=digest(data))
assert len(baseline) == 102314
(HERE / 'starting-files.json').write_text(json.dumps(baseline, indent=2) + '\n')
for name, arguments in {
    'starting-head.txt': ('rev-parse', 'HEAD'), 'starting-main.txt': ('rev-parse', 'origin/main'),
    'starting-local-main.txt': ('rev-parse', 'main'), 'starting-stashes.txt': ('stash', 'list', '--format=%gd %H %s'),
    'starting-worktrees.txt': ('worktree', 'list', '--porcelain')}.items():
    (HERE / name).write_bytes(git(*arguments))
(HERE / 'initial-pull-receipt.json').write_bytes(pull.read_bytes())
raw_pull = Path('/tmp/' + NAME + '-initial-pull.log')
(HERE / 'pull.log').write_bytes(raw_pull.read_bytes())
pull_history = HERE / 'initial-pull-attempts'
pull_history.mkdir()
for suffix in ['.json', '.log', '.limits.json', '.peaks.txt', '.source.py', '.usage.json']:
    path = Path('/tmp/' + NAME + '-initial-pull-1' + suffix)
    shutil.copyfile(path, pull_history / path.name)
shutil.copyfile(raw_pull, pull_history / raw_pull.name)
audit = (ROOT / 'lean/MicroCFTA/Audit.lean').read_bytes()
assert len(audit.splitlines()) == 3131 and digest(audit) == 'b616bb97d542e1494bfbef2d6c3c77365c28731ff8a8a612e59533b44bc783e3'
(HERE / 'original-sources').mkdir()
(HERE / 'original-sources/Audit.original.lean.txt').write_bytes(audit)
(HERE / 'original-source-index.json').write_text(json.dumps(dict(sources=[dict(path='lean/MicroCFTA/Audit.lean',
    snapshot='original-sources/Audit.original.lean.txt', lines=3131, sha256=digest(audit))]), indent=2) + '\n')
for name in ['root-capped-worker.py', 'archive-extra.py', 'haskell-repair-index.md']:
    (HERE / name).write_bytes((PREVIOUS / name).read_bytes())
old_driver = Path('/tmp/mcfta-pair-request-admission-driver.py').read_text()
assert old_driver.count('20261023-pair-request-admission') == 1
driver = old_driver.replace('20261023-pair-request-admission', '20261023-both-miss-native-covered')
(HERE / 'root-driver.py').write_text(driver)
Path('/tmp/' + NAME + '-driver.py').write_text(driver)
target = HERE / 'previous-local-checkpoint'
target.mkdir()
retained = {}
names = [Path('/tmp/mcfta-pair-request-admission-local-publication.json'), push_path]
for stem in ['support-1', 'seal-1', 'local-publication-1', 'authorized-push-1']:
    prefix = 'mcfta-pair-request-admission-' + stem
    for suffix in ['.json', '.log', '.limits.json', '.peaks.txt', '.source.py', '.usage.json']:
        names.append(Path('/tmp') / (prefix + suffix))
names.extend(Path(attempt['log']) for attempt in push['attempts'])
for path in names:
    data = path.read_bytes()
    shutil.copyfile(path, target / path.name)
    retained[path.name] = digest(data)
pull_retained = {path.name: digest(path.read_bytes()) for path in pull_history.iterdir()}
assert len(pull_retained) == 7
(HERE / 'archived-components.json').write_text(json.dumps({'previous-local-checkpoint': retained,
    'initial-pull-attempts': pull_retained}, indent=2) + '\n')
(HERE / 'previous-local-checkpoint.json').write_bytes(names[0].read_bytes())
(HERE / 'previous-authorized-push.json').write_bytes(push_path.read_bytes())
counts = dict(status='PASS', baseline_files=len(baseline),
    older_non_audit_lean=sum(name.startswith('lean/MicroCFTA/') and name.endswith('.lean')
        and name != 'lean/MicroCFTA/Audit.lean' for name in baseline),
    haskell_files=sum(name.endswith('.hs') for name in baseline),
    active_package_files=sum(name.split('/')[0] in {'cfta', 'cfta-generator', 'cfta-ghc', 'decision-model'} for name in baseline),
    original_audit_lines=3131, original_audit_sha256=digest(audit),
    initial_pull_attempts=1, failed_initial_pull_attempts=0, proof_jobs=0,
    previous_postseal_files=len(retained), starting_head=START, backup=backup,
    observed_at=datetime.datetime.now().astimezone().isoformat())
assert (counts['older_non_audit_lean'], counts['haskell_files'], counts['active_package_files']) == (3641, 298, 207)
(HERE / 'baseline-counts.json').write_text(json.dumps(counts, indent=2) + '\n')
(HERE / 'current-progress.md').write_text('''# Native admission through original-row BOTH-miss comparison

The whole formalization goal remains ACTIVE. The previous goal turn made PROGRESS.
H25 proved actual captured pair admission through an observed completed comparison.
Its proof and evidence commits were pushed and remote-verified at6ca7ff763c.
The fresh fast-forward pull and exact file/mode baseline pass.
The next component must derive native Covered at the SAME H13 BOTH-miss receipt.
Use H18 parent admission to derive the actual row-child admission and source scope.
Reuse actual Trace.covered with the derived source branches and literal edgeBody certificate.
Keep the fixed source, concrete holds, finite model, ranks, full Wrapper and all H13 outputs.
Keep pair admission, hidden cluster runs, generated roots and resources separate.
The source-only inventory supplies a route, not a declaration or proof.
Exact declarations and local types require root and independent review.
No body, compiler or prepared evidence tool is authorized yet.
H6 remains strongest combined. FINDINGS keeps the Haskell repair index first.
No Haskell repair, board operation, memory update or ADR is added.
''')
print(json.dumps(counts))
