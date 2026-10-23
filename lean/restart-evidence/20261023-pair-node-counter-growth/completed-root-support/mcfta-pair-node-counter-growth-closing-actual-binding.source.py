exec(compile(open('/tmp/mcfta-pair-node-counter-growth-root-common.py').read(), '/tmp/mcfta-pair-node-counter-growth-root-common.py', 'exec'))
import ast
import datetime
import difflib
import shutil

pending = Path('/tmp/mcfta-pair-node-counter-growth-closing-preparation')
checked_package(pending,'42b4a62a494fb22e8bf85d72dc81d43e3327242efb2ab5e4f71ca53b6a314013','b6e2b2b56bfe79f7c3f0cebaf08f8746724e973c5b703fde665de381e8b234b7')
assert load(HERE / 'root-closing-template-gate.json')['status'] == 'ACCEPTED_PENDING_CLOSING_SOURCE_ONLY'
assert load(HERE / 'root-source-history-review.json')['status'] == 'ACCEPTED_COMPLETE_SELECTED_SOURCE_AND_ACTUAL_HISTORY'
cut = load(HERE / 'actual-proof-cut.json')
metrics = cut['metrics']
bindings = {
    '__H37_AUDIT_LOG_SHA256__':cut['audit']['log_sha256'],
    '__H37_AUDIT_BUILD_JOBS__':str(cut['audit']['build_jobs']),
    '__H37_AUDIT_DEPENDENCIES__':str(cut['audit']['dependencies']),
    '__H37_ACTUAL_JOBS__':str(metrics['actual_jobs']),
    '__H37_FAILED_JOBS__':str(metrics['failed_jobs']),
    '__H37_SOURCE_JOBS__':str(metrics['source_jobs']),
    '__H37_FOCUSED_BUILD_JOBS__':str(metrics['focused_build_jobs']),
    '__H37_AUDIT_JOBS__':str(metrics['audit_jobs']),
    '__H37_WARNED_SOURCE_EXIT_ZERO_JOBS__':str(metrics['warned_source_exit_zero_jobs']),
    '__H37_REJECTED_PUBLIC_TYPE_JOBS__':str(metrics['rejected_public_type_jobs'])}
assert len(bindings) == 10
target = Path('/tmp/mcfta-pair-node-counter-growth-closing-actual-binding')
assert not target.exists()
target.mkdir()
shutil.copytree(pending,target / 'pending-complete')
(target / 'selected').mkdir()
(target / 'diffs').mkdir()
scripts = {}
for source in sorted((pending / 'selected').glob('*.py')):
    before = source.read_text()
    after = before
    for token,value in bindings.items():
        after = after.replace(token,value)
    assert '__H37_' not in after
    path = target / 'selected' / source.name
    path.write_text(after)
    (target / 'diffs' / (source.name + '.patch')).write_text(''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='pending/' + source.name,tofile='selected/' + source.name)))
    (target / 'diffs' / (source.name + '.inverse.patch')).write_text(''.join(difflib.unified_diff(after.splitlines(True),before.splitlines(True),fromfile='selected/' + source.name,tofile='pending/' + source.name)))
    scripts[source.name] = dict(lines=len(after.splitlines()),sha256=sha(path),assertions=sum(isinstance(node,ast.Assert) for node in ast.walk(ast.parse(after))))
assert sum(item['lines'] for item in scripts.values()) == 236 <= 260
assert sum(item['assertions'] for item in scripts.values()) == 59
assert (target / 'selected/verify-seal.py').read_bytes() == (pending / 'selected/verify-seal.py').read_bytes()
(target / 'bindings.json').write_text(json.dumps(bindings,indent=2)+'\n')
(target / 'selected-scripts.json').write_text(json.dumps(scripts,indent=2)+'\n')
for name in ['actual-proof-cut.json','root-source-history-review.json','root-closing-template-gate.json']:
    shutil.copy2(HERE / name,target / name)
(target / 'status.json').write_text(json.dumps(dict(status='ACTUAL_TEN_LITERAL_BINDINGS_SOURCE_ONLY',author='Root',pending_author='Guard',
    pending_complete_retained=True,selected_lines=236,assertions=59,verify_seal_byte_identical=True,
    independent_review_and_Root_acceptance_before_installation=True,selected_execution=False),indent=2)+'\n')
files = {str(path.relative_to(target)):dict(bytes=path.stat().st_size,sha256=sha(path)) for path in sorted(target.rglob('*')) if path.is_file()}
(target / 'pins.json').write_text(json.dumps(files,indent=2)+'\n')
(target / 'FROZEN.json').write_text(json.dumps(dict(status='FROZEN_ACTUAL_CLOSING_BINDING_SOURCE',observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),pins_sha256=sha(target / 'pins.json'),payloads=len(files)),indent=2)+'\n')
print(json.dumps(dict(status='FROZEN',path=str(target),pins_sha256=sha(target / 'pins.json'),frozen_sha256=sha(target / 'FROZEN.json'))))
