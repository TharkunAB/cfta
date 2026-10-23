import datetime
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

ROOT = Path('/home/tritlo/Code/mcfta')
PREVIOUS = ROOT / 'lean/restart-evidence/20261023-fresh-node-counter-growth'
HERE = ROOT / 'lean/restart-evidence/20261023-stored-node-counter-growth'
START = 'af73f5d67493168cbab9cdd58cbc625d80585a23'
PREFIX = 'mcfta-stored-node-counter-growth'
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
publication = json.loads(Path('/tmp/mcfta-fresh-node-counter-growth-local-publication.json').read_bytes())
push = json.loads(Path('/tmp/mcfta-fresh-node-counter-growth-remote-publication.json').read_bytes())
assert publication['status'] == 'LOCAL_PASS' and publication['checkpoint'] == START
assert push['status'] == 'PUSHED_AND_REMOTE_VERIFIED' and push['checkpoint'] == START
assert not HERE.exists()
HERE.mkdir()
backup = 'codex/backup-stored-node-counter-growth-' + datetime.datetime.now().astimezone().strftime('%Y%m%d-%H%M')
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
assert len(baseline) == publication['tracked_blobs_and_modes'] == 116844
save('starting-files.json', baseline)
for name, arguments in {
    'starting-head.txt': ('rev-parse', 'HEAD'), 'starting-main.txt': ('rev-parse', 'origin/main'),
    'starting-local-main.txt': ('rev-parse', 'main'), 'starting-stashes.txt': ('stash', 'list', '--format=%gd %H %s'),
    'starting-worktrees.txt': ('worktree', 'list', '--porcelain')}.items():
    (HERE / name).write_bytes(git(*arguments))
for name in ['root-capped-worker.py', 'archive-extra.py', 'haskell-repair-index.md', 'root-run-check.py']:
    (HERE / name).write_bytes((PREVIOUS / name).read_bytes())
driver = Path('/tmp/mcfta-fresh-node-counter-growth-driver.py').read_text()
assert driver.count('20261023-fresh-node-counter-growth') == 1
driver = driver.replace('20261023-fresh-node-counter-growth', '20261023-stored-node-counter-growth')
(HERE / 'root-driver.py').write_text(driver)
Path('/tmp/' + PREFIX + '-driver.py').write_text(driver)
common = Path('/tmp/mcfta-fresh-node-counter-growth-root-common.py').read_text()
assert common.count('20261023-fresh-node-counter-growth') == 1
common = common.replace('20261023-fresh-node-counter-growth', '20261023-stored-node-counter-growth')
common = common.replace("NAME = 'InternedFreshOrdinaryNodeCounterGrowth'", "NAME = 'InternedFreshOrdinaryStoredNodeCounterGrowth'")
common = common.replace("START = 'ab49ebd03b6f7530c4f48c3b0cff85b85c98b87a'", "START = '" + START + "'")
(HERE / 'root-common.py').write_text(common)
Path('/tmp/' + PREFIX + '-root-common.py').write_text(common)
audit = (ROOT / 'lean/MicroCFTA/Audit.lean').read_bytes()
assert len(audit.splitlines()) == 3141 and sha(audit) == '8257a0517c3ead6de9329d49ccae6cfcf57622f652c2d14a2ff61b9caa3286fd'
(HERE / 'original-sources').mkdir()
(HERE / 'original-sources/Audit.original.lean.txt').write_bytes(audit)
save('original-source-index.json', dict(sources=[dict(path='lean/MicroCFTA/Audit.lean',
    snapshot='original-sources/Audit.original.lean.txt', lines=3141, sha256=sha(audit))]))
components = {}
for component, files in {
    'initial-pull-attempts': [Path('/tmp/' + PREFIX + '-initial-pull.log')] + [Path('/tmp/' + PREFIX + '-initial-pull-1' + suffix) for suffix in ['.json','.log','.limits.json','.peaks.txt','.source.py','.usage.json']],
    'previous-local-checkpoint': [Path('/tmp/mcfta-fresh-node-counter-growth-local-publication.json'), Path('/tmp/mcfta-fresh-node-counter-growth-remote-publication.json')] +
        [Path('/tmp/mcfta-fresh-node-counter-growth-' + stem + suffix) for stem in ['support-1','seal-1','local-publish-1','push-1'] for suffix in ['.json','.log','.limits.json','.peaks.txt','.source.py','.usage.json']]
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
    original_audit_lines=3141, original_audit_sha256=sha(audit), initial_pull_attempts=1,
    failed_initial_pull_attempts=0, proof_jobs=0, starting_head=START, backup=backup,
    observed_at=datetime.datetime.now().astimezone().isoformat())
assert (counts['older_non_audit_lean'], counts['haskell_files'], counts['active_package_files']) == (3651,298,207)
save('baseline-counts.json', counts)
(HERE / 'current-progress.md').write_text('# Repaired stored and optional-binder node-counter growth\n\nH33 was sealed, pushed and remote-verified at af73f5d67493168cbab9cdd58cbc625d80585a23.\nThe next target is actual repaired stored execute, unfold and maybeMu node-counter monotonicity.\nEach result must cover both completed and pending outcomes at the same literal returned heap.\nThe actual callback bound must follow from H33 and Work counters. It must not be a public premise.\nNo Dense, Valid, Facts, Good, Available, closedness or success premise may replace the operational proof.\nBoth probes, ordinaryLevel selection, canonical request and record update must remain literal.\nNative/Scan/H23 lifting, fixed-source initial counter order and domain-history transport remain separate.\nRoom, WordRanges, complete resources, generated execution, Mu/full pass, practical width,\nHaskell and solver correspondence, and convergence remain open.\nNo new body or compiler result is claimed at this bootstrap.\nH6 constructed_node_calls remains strongest combined. The goal is ACTIVE and incomplete.\nNo Haskell repair is proposed. FINDINGS keeps its external repair index first.\nNo board operation, memory write or ADR is added.\n')
print(json.dumps(counts))
