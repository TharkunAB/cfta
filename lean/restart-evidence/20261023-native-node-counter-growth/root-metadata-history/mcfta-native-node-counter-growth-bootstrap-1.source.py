import datetime
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

ROOT = Path('/home/tritlo/Code/mcfta')
PREVIOUS = ROOT / 'lean/restart-evidence/20261023-stored-node-counter-growth'
HERE = ROOT / 'lean/restart-evidence/20261023-native-node-counter-growth'
START = 'a295f1f72153365c886484cbeea933809acbc3f7'
PREFIX = 'mcfta-native-node-counter-growth'
def sha(data):
    return hashlib.sha256(data).hexdigest()
def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)
def save(name, data):
    (HERE / name).write_text(json.dumps(data, indent=2) + '\n')
assert git('rev-parse', 'HEAD').decode().strip() == START
assert git('branch', '--show-current').decode().strip() == 'formalize'
assert not git('status', '--porcelain')
assert json.loads(Path('/tmp/' + PREFIX + '-initial-pull-1.json').read_bytes())['exit_code'] == 0
publication = json.loads(Path('/tmp/mcfta-stored-node-counter-growth-local-publication.json').read_bytes())
push = json.loads(Path('/tmp/mcfta-stored-node-counter-growth-remote-publication.json').read_bytes())
assert publication['status'] == 'LOCAL_PASS' and publication['checkpoint'] == START
assert push['status'] == 'PUSHED_AND_REMOTE_VERIFIED' and push['checkpoint'] == START
assert not HERE.exists()
HERE.mkdir()
backup = 'codex/backup-native-node-counter-growth-' + datetime.datetime.now().astimezone().strftime('%Y%m%d-%H%M')
subprocess.run(['git', 'branch', backup, START], cwd=ROOT, check=True)
(HERE / 'backup-ref.txt').write_text(backup + '\n')
baseline = {}
for raw in git('ls-tree', '-r', '-z', START).split(b'\0'):
    if not raw:
        continue
    metadata, name = raw.split(b'\t', 1)
    mode, kind, blob = metadata.decode().split()
    assert kind == 'blob'
    name = name.decode()
    path = ROOT / name
    data = path.read_bytes()
    assert ('100755' if path.stat().st_mode & 0o111 else '100644') == mode, name
    assert hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest() == blob, name
    baseline[name] = dict(mode=mode, blob=blob, sha256=sha(data))
assert len(baseline) == publication['tracked_blobs_and_modes'] == 118574
save('starting-files.json', baseline)
for name, arguments in {
    'starting-head.txt': ('rev-parse', 'HEAD'), 'starting-main.txt': ('rev-parse', 'origin/main'),
    'starting-local-main.txt': ('rev-parse', 'main'), 'starting-stashes.txt': ('stash', 'list', '--format=%gd %H %s'),
    'starting-worktrees.txt': ('worktree', 'list', '--porcelain')}.items():
    (HERE / name).write_bytes(git(*arguments))
for name in ['root-capped-worker.py', 'archive-extra.py', 'haskell-repair-index.md', 'root-run-check.py']:
    (HERE / name).write_bytes((PREVIOUS / name).read_bytes())
driver = Path('/tmp/mcfta-stored-node-counter-growth-driver.py').read_text()
assert driver.count('20261023-stored-node-counter-growth') == 1
driver = driver.replace('20261023-stored-node-counter-growth', '20261023-native-node-counter-growth')
(HERE / 'root-driver.py').write_text(driver)
Path('/tmp/' + PREFIX + '-driver.py').write_text(driver)
common = Path('/tmp/mcfta-stored-node-counter-growth-root-common.py').read_text()
assert common.count('20261023-stored-node-counter-growth') == 1
common = common.replace('20261023-stored-node-counter-growth', '20261023-native-node-counter-growth')
common = common.replace("NAME = 'InternedFreshOrdinaryStoredNodeCounterGrowth'", "NAME = 'SourceRecursiveIntersectionNativeNodeCounterGrowth'")
common = common.replace("START = 'af73f5d67493168cbab9cdd58cbc625d80585a23'", "START = '" + START + "'")
(HERE / 'root-common.py').write_text(common)
Path('/tmp/' + PREFIX + '-root-common.py').write_text(common)
audit = (ROOT / 'lean/MicroCFTA/Audit.lean').read_bytes()
assert len(audit.splitlines()) == 3142 and sha(audit) == '1f3a43b7fb26827dc930bdddc7d6ee2f0c543cc53821c897ad5062d776f3320f'
(HERE / 'original-sources').mkdir()
(HERE / 'original-sources/Audit.original.lean.txt').write_bytes(audit)
save('original-source-index.json', dict(sources=[dict(path='lean/MicroCFTA/Audit.lean',
    snapshot='original-sources/Audit.original.lean.txt', lines=3142, sha256=sha(audit))]))
components = {}
for component, files in {
    'initial-pull-attempts': [Path('/tmp/' + PREFIX + '-initial-pull.log')] + [Path('/tmp/' + PREFIX + '-initial-pull-1' + suffix) for suffix in ['.json','.log','.limits.json','.peaks.txt','.source.py','.usage.json']],
    'previous-local-checkpoint': [Path('/tmp/mcfta-stored-node-counter-growth-local-publication.json'), Path('/tmp/mcfta-stored-node-counter-growth-remote-publication.json')] +
        [Path('/tmp/mcfta-stored-node-counter-growth-' + stem + suffix) for stem in ['support-1','seal-1','local-publish-1','push-1'] for suffix in ['.json','.log','.limits.json','.peaks.txt','.source.py','.usage.json']]
}.items():
    target = HERE / component
    target.mkdir()
    components[component] = {}
    for path in files:
        shutil.copyfile(path, target / path.name)
        components[component][path.name] = sha(path.read_bytes())
save('archived-components.json', components)
counts = dict(status='PASS', baseline_files=len(baseline),
    older_non_audit_lean=sum(name.startswith('lean/MicroCFTA/') and name.endswith('.lean') and name != 'lean/MicroCFTA/Audit.lean' for name in baseline),
    haskell_files=sum(name.endswith('.hs') for name in baseline),
    active_package_files=sum(name.split('/')[0] in {'cfta','cfta-generator','cfta-ghc','decision-model'} for name in baseline),
    original_audit_lines=3142, original_audit_sha256=sha(audit), initial_pull_attempts=1,
    failed_initial_pull_attempts=0, proof_jobs=0, starting_head=START, backup=backup,
    observed_at=datetime.datetime.now().astimezone().isoformat())
assert (counts['older_non_audit_lean'], counts['haskell_files'], counts['active_package_files']) == (3652,298,207)
save('baseline-counts.json', counts)
(HERE / 'current-progress.md').write_text('# Native node-counter growth\n\nH34 was sealed, pushed and remote-verified at a295f1f72153365c886484cbeea933809acbc3f7.\nThe next target is actual native step, finite execute and resume node-counter growth.\nCompare state.machine.heap.nodes.next with that same projection of the actual returned outcome state.\nCover yielded, done, failed and blocked outcomes for arbitrary initial native states and widths.\nUse existing Work run_next, H34 maybeMu_mono and public immediate memo machine-retention results.\nDo not assume validity, readiness, successful completion, a callback bound or the desired counter bound.\nPending constructor work must retain its actual enlarged heap when native execution blocks.\nFinite execution must compose the actual one-step state with its generalized fuel induction result.\nNo declaration, body or new compiler result is claimed at this bootstrap.\nScan/H23 lifting, fixed-source initial counter order and global domain-history transport remain separate.\nRoom, WordRanges, complete resources, generated execution, Mu/full pass, practical width,\nHaskell and solver correspondence, and convergence remain open.\nH6 constructed_node_calls remains strongest combined. The goal is ACTIVE and incomplete.\nNo Haskell repair is proposed. FINDINGS keeps its external repair index first.\nNo board operation, memory write or ADR is added.\n')
print(json.dumps(counts))
