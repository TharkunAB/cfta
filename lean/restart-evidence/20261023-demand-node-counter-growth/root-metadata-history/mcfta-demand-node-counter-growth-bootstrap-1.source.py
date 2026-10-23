import datetime
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

ROOT = Path('/home/tritlo/Code/mcfta')
PREVIOUS = ROOT / 'lean/restart-evidence/20261023-native-node-counter-growth'
HERE = ROOT / 'lean/restart-evidence/20261023-demand-node-counter-growth'
START = '86b6dd30387c62a1f8f46e1914824695c4a0e908'
PREFIX = 'mcfta-demand-node-counter-growth'

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
publication = json.loads(Path('/tmp/mcfta-native-node-counter-growth-local-publication.json').read_bytes())
push = json.loads(Path('/tmp/mcfta-native-node-counter-growth-remote-publication.json').read_bytes())
assert publication['status'] == 'LOCAL_PASS' and publication['checkpoint'] == START
assert push['status'] == 'PUSHED_AND_REMOTE_VERIFIED' and push['checkpoint'] == START
assert not HERE.exists()
HERE.mkdir()
backup = 'codex/backup-demand-node-counter-growth-' + datetime.datetime.now().astimezone().strftime('%Y%m%d-%H%M')
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
assert len(baseline) == publication['tracked_blobs_and_modes'] == 120276
save('starting-files.json', baseline)
for name, arguments in {
    'starting-head.txt': ('rev-parse', 'HEAD'), 'starting-main.txt': ('rev-parse', 'origin/main'),
    'starting-local-main.txt': ('rev-parse', 'main'), 'starting-stashes.txt': ('stash', 'list', '--format=%gd %H %s'),
    'starting-worktrees.txt': ('worktree', 'list', '--porcelain')}.items():
    (HERE / name).write_bytes(git(*arguments))
assert (HERE / 'starting-main.txt').read_text().strip() == '794903b3fbad3becb8b28736fc33463760731fc7'
assert (HERE / 'starting-local-main.txt').read_text().strip() == 'ed73f5997f1c07e2961d06e6e290d1de38319dad'
for name in ['root-capped-worker.py', 'archive-extra.py', 'haskell-repair-index.md', 'root-run-check.py']:
    (HERE / name).write_bytes((PREVIOUS / name).read_bytes())
driver = (PREVIOUS / 'root-driver.py').read_text()
assert driver.count('20261023-native-node-counter-growth') == 1
driver = driver.replace('20261023-native-node-counter-growth', '20261023-demand-node-counter-growth')
(HERE / 'root-driver.py').write_text(driver)
Path('/tmp/' + PREFIX + '-driver.py').write_text(driver)
common = (PREVIOUS / 'root-common.py').read_text()
assert common.count('20261023-native-node-counter-growth') == 1
assert common.count("NAME = 'SourceRecursiveIntersectionNativeNodeCounterGrowth'") == 1
assert common.count("START = 'a295f1f72153365c886484cbeea933809acbc3f7'") == 1
common = common.replace('20261023-native-node-counter-growth', '20261023-demand-node-counter-growth')
common = common.replace("NAME = 'SourceRecursiveIntersectionNativeNodeCounterGrowth'", "NAME = 'SourceEqualityNativeDemandNodeCounterGrowth'")
common = common.replace("START = 'a295f1f72153365c886484cbeea933809acbc3f7'", "START = '" + START + "'")
(HERE / 'root-common.py').write_text(common)
Path('/tmp/' + PREFIX + '-root-common.py').write_text(common)
audit = (ROOT / 'lean/MicroCFTA/Audit.lean').read_bytes()
assert len(audit.splitlines()) == 3143 and sha(audit) == 'a1554499111eeb145e48d4f537693563e04370349bc2ffea8a352b580f088a76'
(HERE / 'original-sources').mkdir()
(HERE / 'original-sources/Audit.original.lean.txt').write_bytes(audit)
save('original-source-index.json', dict(sources=[dict(path='lean/MicroCFTA/Audit.lean',
    snapshot='original-sources/Audit.original.lean.txt', lines=3143, sha256=sha(audit))]))
components = {}
for component, files in {
    'initial-pull-attempts': [Path('/tmp/' + PREFIX + '-initial-pull.log')] + [Path('/tmp/' + PREFIX + '-initial-pull-1' + suffix) for suffix in ['.json','.log','.limits.json','.peaks.txt','.source.py','.usage.json']],
    'previous-local-checkpoint': [Path('/tmp/mcfta-native-node-counter-growth-local-publication.json'), Path('/tmp/mcfta-native-node-counter-growth-remote-publication.json')] +
        [Path('/tmp/mcfta-native-node-counter-growth-' + stem + suffix) for stem in ['support-1','seal-1','local-publication-1','push-1'] for suffix in ['.json','.log','.limits.json','.peaks.txt','.source.py','.usage.json']]
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
    original_audit_lines=3143, original_audit_sha256=sha(audit), initial_pull_attempts=1,
    failed_initial_pull_attempts=0, proof_jobs=0, starting_head=START, backup=backup,
    observed_at=datetime.datetime.now().astimezone().isoformat())
assert (counts['older_non_audit_lean'], counts['haskell_files'], counts['active_package_files']) == (3653,298,207)
save('baseline-counts.json', counts)
(HERE / 'current-progress.md').write_text('''# Checked-demand node-counter growth

H35 was sealed, pushed and remote-verified at 86b6dd30387c62a1f8f46e1914824695c4a0e908.
The next target is actual checked-demand step, finite execute and resume counter growth.
Compare state.native.machine.heap.nodes.next with that projection of the actual outcome state.
Cover yielded, done, failed, constraintError and blocked outcomes for arbitrary initial states.
Use H35 for forwarded native code, body_native for checked bodies and step_edge_heap for edge demand.
A small private lift projection can follow the four actual native outcome constructors.
Do not assume validity, readiness, input checks, successful completion or a desired counter bound.
Fuel induction must retain the actual yielded control and full checked state.
No declaration, body or compiler result is claimed at this bootstrap.
Pair/Scan/H23 lifting, fixed-source initial counter order and global history remain separate.
Upper resources, Room, WordRanges, generated execution, Mu/full pass, practical width,
Haskell and solver correspondence, and convergence remain open.
H6 constructed_node_calls remains strongest combined. The goal is ACTIVE and incomplete.
No Haskell repair is proposed. FINDINGS keeps its external repair index first.
No board operation, memory write or ADR is added.
''')
print(json.dumps(counts))
