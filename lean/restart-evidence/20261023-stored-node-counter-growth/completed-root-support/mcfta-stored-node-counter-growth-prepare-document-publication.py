exec(compile(open('/tmp/mcfta-stored-node-counter-growth-root-common.py').read(), '/tmp/mcfta-stored-node-counter-growth-root-common.py', 'exec'))
import datetime, difflib
previous = ROOT / 'lean/restart-evidence/20261023-fresh-node-counter-growth'
actual = load(HERE / 'actual-proof-cut.json')
assert actual['metrics'] == dict(actual_jobs=3, source_jobs=2, focused_build_jobs=0, audit_jobs=1,
    failed_jobs=0, warned_source_exit_zero_jobs=0, rejected_public_type_jobs=0)
assert actual['audit']['build_jobs'] == 3653 and actual['audit']['dependencies'] == 75553
assert actual['audit']['log_sha256'] == sha(HERE / 'audit1.log') == 'e077c7b1d57b104aae5c1458febcff0b1a244e60e0c2d3519a798fae6ea25d8a'
def replace_one(text, before, after):
    assert text.count(before) == 1, before
    return text.replace(before, after, 1)
def retain(owner, name, basis, selected):
    (owner / name).write_text(selected)
    (owner / (name + '.basis.txt')).write_text(basis)
    (owner / (name + '.patch')).write_text(''.join(difflib.unified_diff(basis.splitlines(True), selected.splitlines(True), fromfile='H33/' + name, tofile='H34/' + name)))
    (owner / (name + '.inverse.patch')).write_text(''.join(difflib.unified_diff(selected.splitlines(True), basis.splitlines(True), fromfile='H34/' + name, tofile='H33/' + name)))
def freeze(owner, names):
    pins = [dict(path=p.name, bytes=p.stat().st_size, sha256=sha(p)) for p in sorted(owner.iterdir()) if p.is_file()]
    (owner / 'pins.json').write_text(json.dumps(pins, indent=2) + '\n')
    (owner / 'FROZEN.json').write_text(json.dumps(dict(status='FINAL_FROZEN_REVIEW_REQUIRED',
        observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(), pins_count=len(pins), pins_sha256=sha(owner / 'pins.json'),
        selected_lines={name: len((owner / name).read_bytes().splitlines()) for name in names}), indent=2) + '\n')
    print(json.dumps(dict(owner=str(owner), pins_sha256=sha(owner / 'pins.json'), frozen_sha256=sha(owner / 'FROZEN.json'))))
owner = Path('/tmp/mcfta-stored-node-counter-growth-document-preparation')
owner.mkdir()
original = (previous / 'update-documents.py').read_text()
selected = original
for before, after in [('ab49ebd03b6f7530c4f48c3b0cff85b85c98b87a', START),
    ('actual_jobs=5, source_jobs=4', 'actual_jobs=3, source_jobs=2'),
    ('failed_jobs=1, warned_source_exit_zero_jobs=1', 'failed_jobs=0, warned_source_exit_zero_jobs=0'),
    ('audit_build_jobs=3652, audit_dependencies=75541', 'audit_build_jobs=3653, audit_dependencies=75553'),
    ('f5d1bbe1ff0b0e8bafc4c54678f17c0bc1ab259d7541b86d273353a6ef735bb3', actual['audit']['log_sha256']),
    ('lean/notes-current-fresh-node-counter-growth.md', 'lean/notes-current-stored-node-counter-growth.md')]:
    selected = replace_one(selected, before, after)
assert selected.count('public-readback/fresh-node-counter-growth-') == 3
selected = selected.replace('public-readback/fresh-node-counter-growth-', 'public-readback/stored-node-counter-growth-')
retain(owner, 'update-documents.py', original, selected)
for source, target in [('current-update.proposal.md', 'current-update.template.md'), ('focused-note.proposal.md', 'focused-note.template.md')]:
    data = Path('/tmp/mcfta-stored-node-counter-growth-' + source).read_bytes()
    assert data.endswith(b'\n') and b'\r' not in data
    (owner / target).write_bytes(data)
(owner / 'scope.md').write_text('Root adapted the complete H33 writer88 and conditional templates. Actual ledger3/2/0 failed/0 warned source, Audit3653/75553 and exact raw hash are bound. All nine LF inverses and FINDINGS-first repair index guards remain before writes. Three public heads require nine TYPE summary lines. Both actual saved modes and the exact two-file proof commit must precede documents. No selected program ran. This proves only repaired stored executor node counter lower bounds, including pending; H6 remains strongest combined and the goal remains ACTIVE/incomplete. No new Haskell repair is indicated.\n')
freeze(owner, ['update-documents.py'])
owner = Path('/tmp/mcfta-stored-node-counter-growth-publication-preparation')
owner.mkdir()
names = ['proof-commit.py', 'final-publication.py', 'run-standalone-proof-evidence.py']
for name in names:
    original = (previous / name).read_text()
    selected = original.replace('mcfta-fresh-node-counter-growth', 'mcfta-stored-node-counter-growth')
    if name in ['proof-commit.py', 'run-standalone-proof-evidence.py']:
        selected = replace_one(selected, "report['actual_jobs'] == 5", "report['actual_jobs'] == 3")
        selected = replace_one(selected, "report['public_theorems'] == 3 and report['failed_jobs'] == 1", "report['public_theorems'] == 3 and report['failed_jobs'] == 0")
    if name == 'proof-commit.py':
        selected = replace_one(selected, "report['audit_dependencies'] == 75541", "report['audit_dependencies'] == 75553")
        selected = replace_one(selected, 'Prove node counter growth in repaired construction', 'Prove node counter growth in stored execution')
    elif name == 'final-publication.py':
        for before, after in [('20261023-fresh-node-counter-growth', '20261023-stored-node-counter-growth'),
            ('ab49ebd03b6f7530c4f48c3b0cff85b85c98b87a', START),
            ('codex/backup-fresh-node-counter-growth-20261023-1209', 'codex/backup-stored-node-counter-growth-20261023-1350'),
            ('lean/notes-current-fresh-node-counter-growth.md', 'lean/notes-current-stored-node-counter-growth.md'),
            ('Preserve repaired constructor counter proof evidence', 'Preserve stored executor counter proof evidence')]:
            selected = replace_one(selected, before, after)
    retain(owner, name, original, selected)
(owner / 'scope.md').write_text('Root adapted the complete H33 proof committer28, local publisher47 and standalone launcher26. All generic guards remain. Accepted source/history and normal/live PASS from cwd / precede the exact two-file proof commit. Actual ledger3 jobs/3 public/0 failures and Audit75553 are bound. The local publisher checks formalize, backup/main refs, all sealed paths, filesystem/index/HEAD blobs and modes, clean tree and seal. It has no network command. User-authorized Root push follows local verification. No selected program ran.\n')
freeze(owner, names)
