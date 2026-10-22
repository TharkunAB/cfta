import datetime
import hashlib
import json
import shutil
import sys
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
here = root / 'lean/restart-evidence/20261022-original-row-cluster-completion'
review_path, review_sha = sys.argv[1:]
def sha(data):
    return hashlib.sha256(data).hexdigest()
assert sha((here / review_path).read_bytes()) == review_sha
name = 'SourceCurrentOriginalRowClusterCompletion'
source = (here / (name + '.lean')).read_bytes()
selected_sha = 'c6e8e0f7f819d1c595ff6d56c160558bff837a86196ad2c951524d93a70c9a9b'
assert sha(source) == selected_sha and len(source.splitlines()) == 345
strict, full = 'original-row-cluster-completion-strict-3', 'original-row-cluster-completion-public-1'
assert (here / (strict + '.source.lean')).read_bytes() == source
assert (here / (strict + '.log')).read_bytes() == b''
assert json.loads((here / (strict + '.json')).read_text())['exit_code'] == 0
report = json.loads((here / 'public-readback/original-row-cluster-completion-full-readback.json').read_text())
head = report['heads'][0]
checked = (here / 'public-readback/original-row-cluster-completion-cluster_complete-public-type.txt').read_bytes()
printed = (here / 'public-readback/original-row-cluster-completion-cluster_complete-printed-public-type.txt').read_bytes()
assert checked == printed and sha(checked) == '89d3dbda3fc24202f94a9126aa10d9022226455cb91817365798aa1875d128fa'
assert report['log_sha256'] == sha((here / (full + '.log')).read_bytes())
assert head['actual_axioms_within_standard_allowed'] and head['check_print_type_byte_identity']
assert not any(x in checked.decode() for x in ['_private', '✝', '†', '‡', name + '.execute_yielded_add', name + '.scan_boundary_complete'])
assert set(head['actual_axioms']) <= {'Classical.choice', 'Quot.sound', 'propext'}
fields = json.loads((here / 'proof-verifier-preparation-v2/scope-field-map.json').read_text())
review = dict(status='ROOT_ACCEPTED_FOR_OFFICIAL_INSTALL_AND_AUDIT',
    observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    source_sha256=selected_sha, source_lines=345, public_theorem=head['head'],
    complete_public_type_root_review='CLEAR', independent_complete_public_type_review='CLEAR',
    root_read_complete_public_type=True, root_printed_type_byte_identity_verified=True,
    check_print_type_byte_identity=True, four_private_markers_and_all_helpers_absent_from_type=True,
    type_sha256=sha(checked), full_raw_sha256=report['log_sha256'], actual_axioms=sorted(head['actual_axioms']),
    body_retained_and_programmatically_checked=True, whole_body_manual_read_claimed=False,
    independent_review=review_path, independent_review_sha256=review_sha,
    root_whole_type_read_ranges=[[1,135],[136,300],[301,460],[461,len(checked.splitlines())]])
review.update({key: True for key in fields['require_true']})
review.update({key: False for key in fields['require_false']})
relative = 'lean/MicroCFTA/' + name + '.lean'
target = root / relative
original = (here / 'original-sources/Audit.original.lean.txt').read_bytes()
audit = root / 'lean/MicroCFTA/Audit.lean'
assert sha(original) == '2fc4ad7d7e708d0601a46c6053f436be92e7fb03b7be78098ec66a2b9c86a698'
assert audit.read_bytes() == original and not target.exists()
assert not (here / 'root-full-review.json').exists()
assert not (here / 'selected-sources.json').exists() and not (here / 'selected-source-gate.json').exists()
(here / 'root-full-review.json').write_text(json.dumps(review, indent=2) + '\n')
(here / 'selected-sources').mkdir()
snapshot = here / 'selected-sources' / (name + '.lean')
snapshot.write_bytes(source)
(here / 'selected-sources.json').write_text(json.dumps({relative: dict(sha256=selected_sha, lines=345, strict=strict, full=full)}, indent=2) + '\n')
(here / 'selected-source-gate.json').write_text(json.dumps(dict(status='ROOT_ACCEPTED', path=relative,
    sha256=selected_sha, lines=345, snapshot='selected-sources/' + name + '.lean'), indent=2) + '\n')
shutil.copyfile(snapshot, target)
addition = ('import MicroCFTA.' + name + '\n').encode()
assert original.startswith(b'import Lean\n') and addition not in original
audit.write_bytes(original.replace(b'import Lean\n', b'import Lean\n' + addition, 1))
assert audit.read_bytes().replace(addition, b'', 1) == original
print(json.dumps(dict(status='PASS', source_sha256=selected_sha, new_module=relative, only_old_lean_change='one Audit import')))
