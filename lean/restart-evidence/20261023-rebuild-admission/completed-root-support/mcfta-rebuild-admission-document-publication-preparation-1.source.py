exec(compile(open('/tmp/mcfta-rebuild-admission-root-common.py').read(), '/tmp/mcfta-rebuild-admission-root-common.py', 'exec'))
import datetime
import difflib
previous = ROOT / 'lean/restart-evidence/20261023-group-admission'
def replace_one(source, old, new):
    assert source.count(old) == 1, old
    return source.replace(old, new, 1)
def retain_program(owner, name, original, selected):
    (owner / name).write_text(selected)
    (owner / (name + '.basis.txt')).write_text(original)
    (owner / (name + '.patch')).write_text(''.join(difflib.unified_diff(original.splitlines(True), selected.splitlines(True), fromfile='H30/' + name, tofile='H31/' + name)))
    (owner / (name + '.inverse.patch')).write_text(''.join(difflib.unified_diff(selected.splitlines(True), original.splitlines(True), fromfile='H31/' + name, tofile='H30/' + name)))
def freeze(owner, names):
    pins = [dict(path=path.name, bytes=path.stat().st_size, sha256=sha(path)) for path in sorted(owner.iterdir()) if path.is_file()]
    (owner / 'pins.json').write_text(json.dumps(pins, indent=2) + '\n')
    (owner / 'FROZEN.json').write_text(json.dumps(dict(status='FINAL_FROZEN_REVIEW_REQUIRED',
        observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(), pins_count=len(pins),
        pins_sha256=sha(owner / 'pins.json'), selected_lines={name:len((owner / name).read_bytes().splitlines()) for name in names}), indent=2) + '\n')
    print(json.dumps(dict(owner=str(owner), pins_sha256=sha(owner / 'pins.json'), frozen_sha256=sha(owner / 'FROZEN.json'))))
owner = Path('/tmp/mcfta-rebuild-admission-document-preparation')
assert not owner.exists()
owner.mkdir()
basis = previous / 'update-documents.py'
assert sha(basis) == 'fe1376bf0b25182069d1cbdb53ae53e742ba084eb1b5b9c4107fa67f8ec3815a'
original = basis.read_text()
selected = original
for old, new in [('591bda7cd4028ee1ed22770c9974142294c92210', START),
                 ('audit_build_jobs=3649, audit_dependencies=75526', 'audit_build_jobs=3650, audit_dependencies=75527'),
                 ('786f8672ed703d466699fe5d386da0a9c5075009f78c336b1c822a6d0269bf09', '67e44945471d10afe61e050cd8ed472b7649e28c52d053b0741f10c9e138129e'),
                 ('lean/notes-current-group-admission.md', 'lean/notes-current-rebuild-admission.md')]:
    selected = replace_one(selected, old, new)
assert selected.count('public-readback/group-admission-') == 3
selected = selected.replace('public-readback/group-admission-', 'public-readback/rebuild-admission-')
retain_program(owner, 'update-documents.py', original, selected)
for source, target in [('current-update.proposal.md', 'current-update.template.md'), ('focused-note.proposal.md', 'focused-note.template.md')]:
    data = Path('/tmp/mcfta-rebuild-admission-' + source).read_bytes()
    assert data.endswith(b'\n') and b'\r' not in data
    (owner / target).write_bytes(data)
(owner / 'scope.md').write_text('Root adapted the H30 document writer and wrote both H31 templates. All nine LF inverses and FINDINGS repair ordering remain prewrite guards. Both actual saved modes and the exact two-file proof commit must precede all document writes. Actual Audit3650/75527 and its raw hash are bound. The templates state certificate preservation at the same literal H23 after. They keep old-model membership, generated execution, new resources and the whole goal incomplete. They claim no seal or push. No selected program ran.\n')
freeze(owner, ['update-documents.py'])
owner = Path('/tmp/mcfta-rebuild-admission-publication-preparation')
assert not owner.exists()
owner.mkdir()
for name in ['proof-commit.py', 'final-publication.py', 'run-standalone-proof-evidence.py']:
    original = (previous / name).read_text()
    selected = original.replace('mcfta-group-admission', 'mcfta-rebuild-admission')
    if name == 'proof-commit.py':
        selected = replace_one(selected, "report['audit_dependencies'] == 75526", "report['audit_dependencies'] == 75527")
        selected = replace_one(selected, 'Prove admission across original-row symbol groups', 'Prove admission after ordinary reconstruction')
    elif name == 'final-publication.py':
        for old, new in [('20261023-group-admission', '20261023-rebuild-admission'),
                         ('591bda7cd4028ee1ed22770c9974142294c92210', START),
                         ('codex/backup-group-admission-20261023-0925', 'codex/backup-rebuild-admission-20261023-1021'),
                         ('lean/notes-current-group-admission.md', 'lean/notes-current-rebuild-admission.md'),
                         ('Preserve group admission proof evidence', 'Preserve rebuild admission proof evidence')]:
            selected = replace_one(selected, old, new)
    retain_program(owner, name, original, selected)
(owner / 'scope.md').write_text('Root adapted the H30 proof committer28, local publisher47 and standalone launcher26. All generic guards remain. The proof commit requires actual dual-mode PASS and accepted independent source/history review before staging one module and Audit. The launcher verifies accepted program/data hashes and runs both modes at cwd /. The publisher retains branch, backup, main refs, exact scope, all sealed paths, full filesystem/index/HEAD blobs and modes, clean tree and seal checks. It has no network command. Root performs the standing authorized push separately. No selected program ran.\n')
freeze(owner, ['proof-commit.py', 'final-publication.py', 'run-standalone-proof-evidence.py'])
