exec(compile(open('/tmp/mcfta-pair-inventory-rebase-root-common.py').read(), '/tmp/mcfta-pair-inventory-rebase-root-common.py', 'exec'))
import datetime
import difflib
previous = ROOT / 'lean/restart-evidence/20261023-rebuild-admission'
def replace_one(source, old, new):
    assert source.count(old) == 1, old
    return source.replace(old, new, 1)
def retain_program(owner, name, original, selected):
    (owner / name).write_text(selected)
    (owner / (name + '.basis.txt')).write_text(original)
    (owner / (name + '.patch')).write_text(''.join(difflib.unified_diff(original.splitlines(True), selected.splitlines(True), fromfile='H31/' + name, tofile='H32/' + name)))
    (owner / (name + '.inverse.patch')).write_text(''.join(difflib.unified_diff(selected.splitlines(True), original.splitlines(True), fromfile='H32/' + name, tofile='H31/' + name)))
def freeze(owner, names):
    pins = [dict(path=path.name, bytes=path.stat().st_size, sha256=sha(path)) for path in sorted(owner.iterdir()) if path.is_file()]
    (owner / 'pins.json').write_text(json.dumps(pins, indent=2) + '\n')
    (owner / 'FROZEN.json').write_text(json.dumps(dict(status='FINAL_FROZEN_REVIEW_REQUIRED',
        observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(), pins_count=len(pins),
        pins_sha256=sha(owner / 'pins.json'), selected_lines={name:len((owner / name).read_bytes().splitlines()) for name in names}), indent=2) + '\n')
    print(json.dumps(dict(owner=str(owner), pins_sha256=sha(owner / 'pins.json'), frozen_sha256=sha(owner / 'FROZEN.json'))))
actual = load(HERE / 'actual-proof-cut.json')
assert actual['audit']['build_jobs'] == 3651 and actual['audit']['dependencies'] == 75528
assert actual['audit']['log_sha256'] == sha(HERE / 'audit1.log') == '26624ac69192ddd76665e9da66031d6d6b3637ecdae938fd34493d890a5e786f'
owner = Path('/tmp/mcfta-pair-inventory-rebase-document-preparation')
assert not owner.exists()
owner.mkdir()
basis = previous / 'update-documents.py'
assert sha(basis) == '2075b195d06d336fb74328986b58cc8588bcee20003d15a6fa8cffb13ee4cab9'
original = basis.read_text()
selected = original
for old, new in [('825d83243f4e69b39b2211598d92e15c427f88ed', START),
                 ('audit_build_jobs=3650, audit_dependencies=75527', 'audit_build_jobs=3651, audit_dependencies=75528'),
                 ('67e44945471d10afe61e050cd8ed472b7649e28c52d053b0741f10c9e138129e', actual['audit']['log_sha256']),
                 ('lean/notes-current-rebuild-admission.md', 'lean/notes-current-pair-inventory-rebase.md')]:
    selected = replace_one(selected, old, new)
assert selected.count('public-readback/rebuild-admission-') == 3
selected = selected.replace('public-readback/rebuild-admission-', 'public-readback/pair-inventory-rebase-')
retain_program(owner, 'update-documents.py', original, selected)
for source, target in [('current-update.proposal.md', 'current-update.template.md'), ('focused-note.proposal.md', 'focused-note.template.md')]:
    data = Path('/tmp/mcfta-pair-inventory-rebase-' + source).read_bytes()
    assert data.endswith(b'\n') and b'\r' not in data
    (owner / target).write_bytes(data)
(owner / 'scope.md').write_text('Root adapted the complete H31 writer88 and wrote both H32 templates. All nine LF inverses and FINDINGS repair ordering remain prewrite guards. Both actual saved modes and the exact two-file proof commit precede all document writes. Actual Audit3651/75528 and its raw hash are bound. The proof retains native admission, pair laws and exact old ranks at the same Wrapper in the computed inventory. New execution, resources, original global allocation Trace transport, strict growth and the whole goal remain unproved. No selected program ran.\n')
freeze(owner, ['update-documents.py'])
owner = Path('/tmp/mcfta-pair-inventory-rebase-publication-preparation')
assert not owner.exists()
owner.mkdir()
expected = {'proof-commit.py':'a848614d926e92a18ab8bd7d96212c2d07755be2830559071d4715477d319258',
    'final-publication.py':'7673b8290c64f6d4f5ba8785619e394ba86020bcca66a556fcd080c017583ee5',
    'run-standalone-proof-evidence.py':'e3c0f35af89ea06a4014698cf3909923de35fedd44bddb88be63b9e344da79b1'}
for name in expected:
    assert sha(previous / name) == expected[name]
    original = (previous / name).read_text()
    selected = original.replace('mcfta-rebuild-admission', 'mcfta-pair-inventory-rebase')
    if name == 'proof-commit.py':
        selected = replace_one(selected, "report['audit_dependencies'] == 75527", "report['audit_dependencies'] == 75528")
        selected = replace_one(selected, 'Prove admission after ordinary reconstruction', 'Preserve cached pair meaning in the enlarged inventory')
    elif name == 'final-publication.py':
        for old, new in [('20261023-rebuild-admission', '20261023-pair-inventory-rebase'),
                         ('825d83243f4e69b39b2211598d92e15c427f88ed', START),
                         ('codex/backup-rebuild-admission-20261023-1021', 'codex/backup-pair-inventory-rebase-20261023-1112'),
                         ('lean/notes-current-rebuild-admission.md', 'lean/notes-current-pair-inventory-rebase.md'),
                         ('Preserve rebuild admission proof evidence', 'Preserve pair inventory rebase proof evidence')]:
            selected = replace_one(selected, old, new)
    retain_program(owner, name, original, selected)
(owner / 'scope.md').write_text('Root adapted the complete H31 proof committer28, local publisher47 and standalone launcher26. All generic guards remain. Accepted source/history and actual normal/live PASS precede the exact two-file proof commit. The launcher checks accepted program/data hashes and runs at cwd /. The local publisher checks branch, backup, main refs, scope, all sealed paths, complete filesystem/index/HEAD blobs and modes, clean tree and seal. It executes no network command. The authorized Root push follows the verified local checkpoint. No selected program ran.\n')
freeze(owner, list(expected))
