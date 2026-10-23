exec(compile(open('/tmp/mcfta-pair-node-counter-growth-root-common.py').read(), '/tmp/mcfta-pair-node-counter-growth-root-common.py', 'exec'))
import datetime
import difflib
import shutil

original = Path('/tmp/mcfta-pair-node-counter-growth-document-preparation')
checked_package(original,'32da844f03b20e6ee1ab68216bba308c2a6ec163d8a634ebac8cf24f913839f1','6468cbd0a9b156ffe371f291e670f193702695b54caa93769181d8abb313c927')
target = Path('/tmp/mcfta-pair-node-counter-growth-document-preparation-v2')
assert not target.exists()
target.mkdir()
shutil.copytree(original,target / 'original-v1')
for name in load(original / 'pins.json'):
    shutil.copy2(original / name,target / name)
changes = [
    ('current-update.template.md','No earlier source, constructor order or counterexample changes.','No earlier implementation or proof body, constructor order or counterexample changes.'),
    ('focused-note.template.md','No older source, draft, counterexample or optimized core changes.','No older proof body, draft, counterexample or optimized core changes.')]
patch = ''
for name,before,after in changes:
    old = (target / name).read_text()
    assert old.count(before) == 1
    new = old.replace(before,after)
    (target / name).write_text(new)
    patch += ''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='original-v1/' + name,tofile=name))
assert (target / 'update-documents.py').read_bytes() == (original / 'update-documents.py').read_bytes()
(target / 'scope-wording.patch').write_text(patch)
(target / 'scope-wording-correction.json').write_text(json.dumps(dict(status='TWO_PAYLOAD_WORDING_CORRECTIONS_ONLY',
    reason='Audit adds one import. Qualify preservation statements to existing implementation and proof bodies.',
    changed_payloads=[name for name,_before,_after in changes],
    writer_and_all_guards_unchanged=True,complete_V1_retained=True,
    no_proof_source_or_compiler_change=True),indent=2)+'\n')
files = {str(path.relative_to(target)):dict(bytes=path.stat().st_size,sha256=sha(path)) for path in sorted(target.rglob('*')) if path.is_file()}
(target / 'pins.json').write_text(json.dumps(files,indent=2)+'\n')
(target / 'FROZEN.json').write_text(json.dumps(dict(status='FROZEN_DOCUMENT_SOURCE_AND_PAYLOADS_V2',observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),pins_sha256=sha(target / 'pins.json'),payloads=len(files)),indent=2)+'\n')
print(json.dumps(dict(status='FROZEN',path=str(target),pins_sha256=sha(target / 'pins.json'),frozen_sha256=sha(target / 'FROZEN.json'))))
