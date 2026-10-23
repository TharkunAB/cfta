exec(compile(open('/tmp/mcfta-group-admission-root-common.py').read(), '/tmp/mcfta-group-admission-root-common.py', 'exec'))
import datetime
import difflib
owner = Path('/tmp/mcfta-group-admission-publication-preparation')
assert not owner.exists()
previous = ROOT / 'lean/restart-evidence/20261023-cluster-admission'
bases = {
    'proof-commit.py': previous / 'proof-commit.py',
    'final-publication.py': previous / 'publication-preparation/final-publication.py',
    'run-standalone-proof-evidence.py': Path('/tmp/mcfta-cluster-admission-run-standalone-proof-evidence.py')}
assert sha(bases['proof-commit.py']) == '729843f89b8e4c68f0c5476ac1bee16405e021279c5b1e11efd426676813111b'
assert sha(bases['final-publication.py']) == 'b4fa4c716e6b04e0e74211ce72b10c21e73a3564a1cd7c1cea5045cb34b60863'
owner.mkdir()
for name, path in bases.items():
    original = path.read_text()
    selected = original.replace('mcfta-cluster-admission', 'mcfta-group-admission')
    if name in ['proof-commit.py', 'run-standalone-proof-evidence.py']:
        for old, new in [("report['actual_jobs'] == 12", "report['actual_jobs'] == 3"),
                         ("report['selected_modules'] == 3", "report['selected_modules'] == 1"),
                         ("report['public_theorems'] == 6", "report['public_theorems'] == 1"),
                         ("report['failed_jobs'] == 3", "report['failed_jobs'] == 0")]:
            assert selected.count(old) == 1, old
            selected = selected.replace(old, new, 1)
    if name == 'proof-commit.py':
        for old, new in [("report['audit_dependencies'] == 75525", "report['audit_dependencies'] == 75526"),
                         ('assert len(selected) == 3', 'assert len(selected) == 1'),
                         ('Prove admission through original-row symbol clusters', 'Prove admission across original-row symbol groups')]:
            assert selected.count(old) == 1
            selected = selected.replace(old, new, 1)
    elif name == 'final-publication.py':
        for old, new in [('20261023-cluster-admission', '20261023-group-admission'),
                         ('3a4cda624829e03055496857356d6edc9f0b4d74', START),
                         ('codex/backup-cluster-admission-20261023-0712', 'codex/backup-group-admission-20261023-0925'),
                         ('lean/notes-current-cluster-admission.md', 'lean/notes-current-group-admission.md'),
                         ('Preserve cluster admission proof evidence', 'Preserve group admission proof evidence')]:
            assert selected.count(old) == 1, old
            selected = selected.replace(old, new, 1)
    else:
        for old, new in [('root-proof-verifier-v2-review.json', 'root-proof-verifier-review.json'),
                         ('ACCEPTED_WHOLE_REVIEWED_V2_FOR_STANDALONE_DUAL_MODE_EXECUTION', 'ACCEPTED_WHOLE_REVIEWED_FOR_STANDALONE_DUAL_MODE_EXECUTION')]:
            assert selected.count(old) == 1
            selected = selected.replace(old, new, 1)
    (owner / name).write_text(selected)
    (owner / (name + '.basis.txt')).write_text(original)
    (owner / (name + '.patch')).write_text(''.join(difflib.unified_diff(original.splitlines(True), selected.splitlines(True), fromfile='H29/' + name, tofile='H30/' + name)))
    (owner / (name + '.inverse.patch')).write_text(''.join(difflib.unified_diff(selected.splitlines(True), original.splitlines(True), fromfile='H30/' + name, tofile='H29/' + name)))
(owner / 'scope.md').write_text('Root adapted the proof committer, local publisher and standalone verifier launcher. Read all source before execution. The proof committer requires actual dual-mode PASS and the independently accepted source/history gate. It stages exactly one new module and Audit. The local publisher retains every seal, branch, backup, main ref, staging, old sealed-path, full filesystem/index/HEAD blob/mode and clean-tree guard. It has no network command. Root pushes separately under standing authorization. The launcher requires the whole-reviewed actual verifier and data hashes. It runs both saved modes from cwd / before the proof commit. These programs do not compile Lean. This preparation performs no repository mutation.\n')
pins = [dict(path=path.name, bytes=path.stat().st_size, sha256=sha(path)) for path in sorted(owner.iterdir()) if path.is_file()]
(owner / 'pins.json').write_text(json.dumps(pins, indent=2) + '\n')
(owner / 'FROZEN.json').write_text(json.dumps(dict(status='FINAL_FROZEN_REVIEW_REQUIRED',
    observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(), pins_count=len(pins),
    pins_sha256=sha(owner / 'pins.json'), selected_lines={name:len((owner / name).read_text().splitlines()) for name in bases}), indent=2) + '\n')
print(json.dumps(dict(owner=str(owner), pins_sha256=sha(owner / 'pins.json'), frozen_sha256=sha(owner / 'FROZEN.json'))))
