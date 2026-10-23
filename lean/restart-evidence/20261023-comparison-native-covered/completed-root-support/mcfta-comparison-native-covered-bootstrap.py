import datetime
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

ROOT = Path('/home/tritlo/Code/mcfta')
PREVIOUS = ROOT / 'lean/restart-evidence/20261023-completed-hit-readback'
HERE = ROOT / 'lean/restart-evidence/20261023-comparison-native-covered'
START = 'b796e8e660a73ac328d41cad53c61099ba79d93f'
NAME = 'mcfta-comparison-native-covered'

def digest(data):
    return hashlib.sha256(data).hexdigest()

def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)

assert git('rev-parse', 'HEAD').decode().strip() == START
assert git('branch', '--show-current').decode().strip() == 'formalize'
assert not git('status', '--porcelain')
pull = Path('/tmp/' + NAME + '-initial-pull-1.json')
assert json.loads(pull.read_bytes())['exit_code'] == 0
push_path = Path('/tmp/mcfta-completed-hit-readback-authorized-push.json')
push = json.loads(push_path.read_bytes())
assert push['status'] == 'PUSHED_AND_REMOTE_VERIFIED' and push['checkpoint'] == START
previous_publication = json.loads(Path('/tmp/mcfta-completed-hit-readback-local-publication.json').read_bytes())
assert previous_publication['status'] == 'LOCAL_PASS' and previous_publication['checkpoint'] == START
assert not HERE.exists()
HERE.mkdir()
backup = 'codex/backup-comparison-native-covered-' + datetime.datetime.now().astimezone().strftime('%Y%m%d-%H%M')
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
assert len(baseline) == previous_publication['tracked_blobs_and_modes'] == 106098
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
assert len(audit.splitlines()) == 3133
(HERE / 'original-sources').mkdir()
(HERE / 'original-sources/Audit.original.lean.txt').write_bytes(audit)
(HERE / 'original-source-index.json').write_text(json.dumps(dict(sources=[dict(path='lean/MicroCFTA/Audit.lean',
    snapshot='original-sources/Audit.original.lean.txt', lines=3133, sha256=digest(audit))]), indent=2) + '\n')
for name in ['root-capped-worker.py', 'archive-extra.py', 'haskell-repair-index.md']:
    (HERE / name).write_bytes((PREVIOUS / name).read_bytes())
old_driver = Path('/tmp/mcfta-completed-hit-readback-driver.py').read_text()
assert old_driver.count('20261023-completed-hit-readback') == 1
driver = old_driver.replace('20261023-completed-hit-readback', '20261023-comparison-native-covered')
(HERE / 'root-driver.py').write_text(driver)
Path('/tmp/' + NAME + '-driver.py').write_text(driver)
target = HERE / 'previous-local-checkpoint'
target.mkdir()
names = [Path('/tmp/mcfta-completed-hit-readback-local-publication.json'), push_path]
for stem in ['support-1', 'seal-1', 'local-publication-1', 'authorized-push-1',
        'authorized-push-recovery-1', 'push-diagnostics-1', 'authorized-push-recovery-2']:
    prefix = 'mcfta-completed-hit-readback-' + stem
    for suffix in ['.json', '.log', '.limits.json', '.peaks.txt', '.source.py', '.usage.json']:
        names.append(Path('/tmp') / (prefix + suffix))
names.extend(Path(attempt['log']) for attempt in push['attempts'])
retained = {}
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
    original_audit_lines=3133, original_audit_sha256=digest(audit), initial_pull_attempts=1,
    failed_initial_pull_attempts=0, proof_jobs=0, previous_postseal_files=len(retained),
    starting_head=START, backup=backup, observed_at=datetime.datetime.now().astimezone().isoformat())
assert (counts['older_non_audit_lean'], counts['haskell_files'], counts['active_package_files']) == (3643, 298, 207)
(HERE / 'baseline-counts.json').write_text(json.dumps(counts, indent=2) + '\n')
(HERE / 'current-progress.md').write_text('''# Native coverage through one original-row comparison

The whole formalization goal remains ACTIVE. The previous goal turn made PROGRESS.
H27 proved checked-state equality for the SAME observed completed pair-cache hit.
Its proof and evidence commits were pushed and remote-verified at b796e8e660a.
The fresh fast-forward pull and exact file/mode baseline pass.
This component must append native Covered to one actual H15 comparison.
Keep its SAME fuel, result, full after and all twelve outputs.
Fix one finite input, its exact model/ranks/holds and the populated cache.
Require genuine parent admission and incoming Covered. Keep arbitrary initialDomains,
Valid, the SAME global domain Trace and one genuine global Room at fixed width.
H27 handles the SAME completed hit. A miss needs public raw Steps, actual
admission and prefix-derived physical Trace at those same checked endpoints.
Only the emptyDomain request has no binding obligations. Source bindings can be nonempty.
No hidden H15 receipt, second completion, new resource or generated-parent oracle is supplied.
The reviewed route authorizes no header, body or compiler job.
Exact declarations/local types and the proposed whole-source cap230 need root and independent review.
H6 remains strongest combined. FINDINGS keeps the Haskell repair index first.
No Haskell repair, board operation, memory update or ADR is added.
''')
print(json.dumps(counts))
