import datetime
import hashlib
import json
import shutil
import sys
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
here = root / 'lean/restart-evidence/20261022-original-row-cluster-language'
review_path, review_sha, type_sha, raw_sha, source_sha, source_lines, strict, full, verifier_component = sys.argv[1:]
source_lines = int(source_lines)
def sha(data):
    return hashlib.sha256(data).hexdigest()
assert sha((here / review_path).read_bytes()) == review_sha
name = 'SourceCurrentOriginalRowClusterLanguage'
source = (here / (name + '.lean')).read_bytes()
assert sha(source) == source_sha and len(source.splitlines()) == source_lines <= 500
assert (here / (strict + '.source.lean')).read_bytes() == source
assert (here / (strict + '.log')).read_bytes() == b''
assert json.loads((here / (strict + '.json')).read_text())['exit_code'] == 0
report = json.loads((here / 'public-readback/original-row-cluster-language-full-readback.json').read_text())
assert len(report['heads']) == 1 and report['source_sha256'] == source_sha
head = report['heads'][0]
assert head['head'] == 'MicroCFTA.' + name + '.cluster_complete'
checked = (here / 'public-readback/original-row-cluster-language-cluster_complete-public-type.txt').read_bytes()
printed = (here / 'public-readback/original-row-cluster-language-cluster_complete-printed-public-type.txt').read_bytes()
assert checked == printed and sha(checked) == type_sha
assert report['log_sha256'] == sha((here / (full + '.log')).read_bytes()) == raw_sha
assert head['actual_axioms_within_standard_allowed'] and head['check_print_type_byte_identity']
assert not any(x in checked.decode() for x in ['_private', '✝', '†', '‡'])
assert head['private_namespace_helpers_checked'] == ['execute_yielded_add', 'scan_boundary_complete']
assert set(head['actual_axioms']) <= {'Classical.choice', 'Quot.sound', 'propext'}
fields = json.loads((here / verifier_component / 'scope-field-map.json').read_text())
review = dict(status='ROOT_ACCEPTED_FOR_OFFICIAL_INSTALL_AND_AUDIT',
    observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    source_sha256=source_sha, source_lines=source_lines, public_theorem=head['head'],
    complete_public_type_root_review='CLEAR', independent_complete_public_type_review='CLEAR',
    root_read_complete_public_type=True, root_printed_type_byte_identity_verified=True,
    check_print_type_byte_identity=True, four_private_markers_and_all_helpers_absent_from_type=True,
    type_sha256=sha(checked), full_raw_sha256=report['log_sha256'], actual_axioms=sorted(head['actual_axioms']),
    body_retained_and_programmatically_checked=True, whole_body_manual_read_claimed=False,
    independent_review=review_path, independent_review_sha256=review_sha,
    root_whole_type_read_ranges=[[1, len(checked.splitlines())]])
review.update({key: True for key in fields['required_true']})
review.update({key: False for key in fields['required_false']})
relative = 'lean/MicroCFTA/' + name + '.lean'
target = root / relative
audit = root / 'lean/MicroCFTA/Audit.lean'
original = (here / 'original-sources/Audit.original.lean.txt').read_bytes()
assert sha(original) == '7e754f81ab43baeace185b866adaf0a38c61ab347b402752cf83bba73882de5e'
assert len(original.splitlines()) == 3125 and audit.read_bytes() == original
assert json.loads((here / 'original-source-index.json').read_text()) == dict(sources=[dict(
    path='lean/MicroCFTA/Audit.lean', snapshot='original-sources/Audit.original.lean.txt',
    lines=3125, sha256=sha(original))])
assert json.loads((here / 'starting-files.json').read_text())['lean/MicroCFTA/Audit.lean']['sha256'] == sha(original)
addition = ('import MicroCFTA.' + name + '\n').encode()
assert original.startswith(b'import Lean\n') and addition not in original
assert not target.exists() and not (here / 'selected-sources').exists()
assert all(not (here / item).exists() for item in ['root-full-review.json', 'selected-sources.json', 'selected-source-gate.json'])
(here / 'root-full-review.json').write_text(json.dumps(review, indent=2) + '\n')
(here / 'selected-sources').mkdir()
snapshot = here / 'selected-sources' / (name + '.lean')
snapshot.write_bytes(source)
(here / 'selected-sources.json').write_text(json.dumps({relative: dict(
    sha256=source_sha, lines=source_lines, strict=strict, full=full)}, indent=2) + '\n')
(here / 'selected-source-gate.json').write_text(json.dumps(dict(status='ROOT_ACCEPTED', path=relative,
    sha256=source_sha, lines=source_lines, snapshot='selected-sources/' + name + '.lean'), indent=2) + '\n')
shutil.copyfile(snapshot, target)
audit.write_bytes(original.replace(b'import Lean\n', b'import Lean\n' + addition, 1))
assert audit.read_bytes().replace(addition, b'', 1) == original
print(json.dumps(dict(status='PASS', source_sha256=source_sha, new_module=relative,
    only_old_lean_change='one Audit import')))
