exec(compile(open('/tmp/mcfta-group-admission-root-common.py').read(), '/tmp/mcfta-group-admission-root-common.py', 'exec'))
import datetime
import difflib
owner = Path('/tmp/mcfta-group-admission-document-preparation')
assert not owner.exists()
basis = ROOT / 'lean/restart-evidence/20261023-cluster-admission/update-documents.py'
assert sha(basis) == '590e6154608b461632d454dbf1dd97f86f4b1e68b0a574fd91545e01d1da4688'
original = basis.read_text()
selected = original
substitutions = [
    ("START = '3a4cda624829e03055496857356d6edc9f0b4d74'", "START = '591bda7cd4028ee1ed22770c9974142294c92210'"),
    ('actual_jobs=12, source_jobs=9, focused_build_jobs=2, audit_jobs=1,', 'actual_jobs=3, source_jobs=2, focused_build_jobs=0, audit_jobs=1,'),
    ('failed_jobs=3, warned_source_exit_zero_jobs=0, rejected_public_type_jobs=0,', 'failed_jobs=0, warned_source_exit_zero_jobs=0, rejected_public_type_jobs=0,'),
    ('selected_modules=3, public_theorems=6, audit_build_jobs=3648, audit_dependencies=75525)', 'selected_modules=1, public_theorems=1, audit_build_jobs=3649, audit_dependencies=75526)'),
    ('866c966deeb27dce926e5ac2476e4f132f9f211969e5db59e4851e8bf6eb6631', '786f8672ed703d466699fe5d386da0a9c5075009f78c336b1c822a6d0269bf09'),
    ('assert len(selection) == 3', 'assert len(selection) == 1'),
    ("'public-readback/cluster-admission-' + group + '-full-readback.json'", "'public-readback/group-admission-full-readback.json'"),
    ("'public-readback/cluster-admission-' + group + '-' + short + '-public-type.txt'", "'public-readback/group-admission-' + short + '-public-type.txt'"),
    ("'public-readback/cluster-admission-' + group + '-' + short + '-printed-public-type.txt'", "'public-readback/group-admission-' + short + '-printed-public-type.txt'"),
    ('assert len(type_summary) == 18', 'assert len(type_summary) == 3'),
    ('lean/notes-current-cluster-admission.md', 'lean/notes-current-group-admission.md')]
for old, new in substitutions:
    assert selected.count(old) == 1, old
    selected = selected.replace(old, new, 1)
begin = selected.index("for group in ['execution', 'boundary', 'outer']:\n")
end = selected.index('assert len(type_summary) == 3\n', begin)
block = selected[begin:end].splitlines(True)
assert all(line.startswith('    ') for line in block[1:])
selected = selected[:begin] + ''.join(line[4:] for line in block[1:]) + selected[end:]
owner.mkdir()
(owner / 'update-documents.py').write_text(selected)
(owner / 'basis-H29-update-documents.py').write_text(original)
(owner / 'exact.patch').write_text(''.join(difflib.unified_diff(original.splitlines(True), selected.splitlines(True), fromfile='H29/update-documents.py', tofile='H30/update-documents.py')))
(owner / 'inverse.patch').write_text(''.join(difflib.unified_diff(selected.splitlines(True), original.splitlines(True), fromfile='H30/update-documents.py', tofile='H29/update-documents.py')))
for source, target in [('current-update.proposal.md', 'current-update.template.md'), ('focused-note.proposal.md', 'focused-note.template.md')]:
    data = Path('/tmp/mcfta-group-admission-' + source).read_bytes()
    assert data.endswith(b'\n') and b'\r' not in data
    (owner / target).write_bytes(data)
(owner / 'scope.json').write_text(json.dumps(dict(status='REVIEW_REQUIRED_BEFORE_INSTALL_OR_EXECUTION',
    author='Root', whole_basis_lines=89, selected_lines=len(selected.splitlines()),
    actual_metrics=load(HERE / 'actual-proof-cut.json'),
    substitutions=[dict(old=old, new=new) for old, new in substitutions],
    nine_document_prewrite_inverses_retained=True, findings_repair_index_first=True,
    requires_both_actual_saved_verifier_modes_and_exact_proof_commit=True,
    no_document_or_repository_write_performed=True), indent=2) + '\n')
pins = [dict(path=str(path.relative_to(owner)), bytes=path.stat().st_size, sha256=sha(path)) for path in sorted(owner.rglob('*')) if path.is_file()]
(owner / 'pins.json').write_text(json.dumps(pins, indent=2) + '\n')
(owner / 'FROZEN.json').write_text(json.dumps(dict(status='FINAL_FROZEN_REVIEW_REQUIRED',
    observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    pins_count=len(pins), pins_sha256=sha(owner / 'pins.json'), selected_sha256=sha(owner / 'update-documents.py')),
    indent=2) + '\n')
print(json.dumps(dict(owner=str(owner), pins_sha256=sha(owner / 'pins.json'), frozen_sha256=sha(owner / 'FROZEN.json'), selected_sha256=sha(owner / 'update-documents.py'), lines=len(selected.splitlines()))))
