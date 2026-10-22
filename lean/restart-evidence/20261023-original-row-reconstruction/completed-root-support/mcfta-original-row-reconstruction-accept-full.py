import datetime
import hashlib
import json
import runpy
import sys
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
here = root / 'lean/restart-evidence/20261023-original-row-reconstruction'
audit = Path('/tmp/mcfta-original-row-reconstruction-public-audit')
digest = lambda data: hashlib.sha256(data).hexdigest()
load = lambda path: json.loads(path.read_bytes())
assert not (here / 'root-full-review.json').exists()
pins = load(audit / 'pins.json')
rows = pins if isinstance(pins, list) else [dict(path=path, **item) for path, item in pins.items()]
for item in rows:
    data = (audit / item['path']).read_bytes()
    assert len(data) == item['bytes'] and digest(data) == item['sha256']
independent = load(audit / 'review.json')
freeze = load(audit / 'FROZEN.json')
assert independent['status'] == 'CLEAR'
assert freeze['review_json_sha256'] == digest((audit / 'review.json').read_bytes()) == '67c899d173c2ca9a0e3b84a28f23528deb97ba7168cea66b0a2176279addfc72'
assert freeze['pins_sha256'] == digest((audit / 'pins.json').read_bytes())
assert independent['checked_type']['personally_read_every_line'] is True
source = (here / 'SourceCurrentOriginalRowReconstruction.lean').read_bytes()
assert digest(source) == '69ed5b8d01f7bcd1d21aa4a66206c9f0bc9480c728c695bfafd7e8222621e435'
assert independent['source_sha256'] == digest(source)
assert len(source.splitlines()) == 210
report = load(here / 'public-readback/original-row-reconstruction-full-readback.json')
assert report['source_sha256'] == digest(source) and report['owned_public_job_exit'] == 0
head, = report['heads']
checked = (here / 'public-readback/original-row-reconstruction-ordinary_complete-public-type.txt').read_bytes()
printed = (here / 'public-readback/original-row-reconstruction-ordinary_complete-printed-public-type.txt').read_bytes()
assert checked == printed and digest(checked) == '41b97f6d0dc108847e84ef67e0011a880bc222ec1849513161649bb2a031e5bb'
assert len(checked.splitlines()) == 1951 and head['check_print_type_byte_identity'] is True
assert head['actual_axioms'] == ['Classical.choice', 'Quot.sound', 'propext']
for filename, item in report['retained_slices'].items():
    data = (here / 'public-readback' / filename).read_bytes()
    assert len(data) == item['bytes'] and digest(data) == item['sha256']
raw = (here / 'original-row-reconstruction-public-1.log').read_bytes()
assert digest(raw) == report['log_sha256'] == '6b234343f2185f8a9c889ef4c165d8298024155a30b40da0e9f83336080a94a3'
assert (here / 'original-row-reconstruction-strict-2.log').read_bytes() == b''
sys.argv = ['archive-extra.py', str(audit), 'public-audit']
runpy.run_path(str(here / 'archive-extra.py'), run_name='__main__')
review = dict(status='ROOT_ACCEPTED_FOR_OFFICIAL_INSTALL_AND_AUDIT', source_sha256=digest(source),
    source_lines=210, public_heads=[head['head']], complete_public_type_root_review='CLEAR',
    independent_complete_public_type_review='CLEAR', root_read_complete_public_types=True,
    four_private_markers_and_all_helpers_absent_from_type=True,
    types_sha256={'ordinary_complete': digest(checked)}, full_raw_sha256=digest(raw),
    actual_axioms_by_head={'ordinary_complete': head['actual_axioms']},
    body_retained_and_programmatically_checked=True, whole_body_manual_read_claimed=False,
    root_printed_type_lexical_identity_verified=True,
    raw_type_byte_identity_by_head={'ordinary_complete': True}, root_printed_type_byte_identity_verified=True,
    observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    independent_review='public-audit/review.json', independent_review_sha256=digest((audit / 'review.json').read_bytes()),
    complete_checked_type_lines=1951, complete_checked_type_bytes=len(checked),
    root_manual_read_scope='All 1951 logical checked TYPE lines, with leading ASCII spaces removed for display only. Raw bytes stay unchanged. Actual axioms and source210 read. Printed TYPE and whole BODY checked programmatically; no whole BODY manual read claim.')
for key in ['ordinary_original_reconstruction_derived', 'same_last_group_state_constructor_run',
    'raw_checked_makeNode_execute_two_derived', 'fixed_model_stable_heap_transport_derived',
    'all_ambient_physical_parent_equivalence_derived']:
    review[key] = True
for key in ['future_success_premise', 'fresh_key_width_safety_claimed', 'generated_root_admission_claimed',
    'model_rebase_claimed', 'mu_reconstruction_claimed', 'public_pass_claimed',
    'haskell_refinement_claimed', 'whole_goal_complete']:
    review[key] = False
(here / 'root-full-review.json').write_text(json.dumps(review, indent=2) + '\n')
target = root / 'lean/MicroCFTA/SourceCurrentOriginalRowReconstruction.lean'
assert not target.exists()
original = (here / 'original-sources/Audit.original.lean.txt').read_bytes()
aggregate = root / 'lean/MicroCFTA/Audit.lean'
assert aggregate.read_bytes() == original
addition = b'import MicroCFTA.SourceCurrentOriginalRowReconstruction\n'
assert addition not in original
offset = original.index(b'/-!')
target.write_bytes(source)
aggregate.write_bytes(original[:offset] + addition + original[offset:])
assert aggregate.read_bytes().replace(addition, b'', 1) == original
with (here / 'current-progress.md').open('a') as stream:
    stream.write('\n## Complete public statement accepted\n\n'
        'The sole FULL passes. Root and independent reviews read the complete checked TYPE.\n'
        'Checked and printed TYPE bytes are identical. Only the three standard axioms occur.\n'
        'The exact selected module and single inverse Audit import are installed.\n'
        'The aggregate Audit remains pending. The first strict failure remains retained.\n'
        'Whole proof BODY retention is programmatic. The whole formalization goal stays ACTIVE.\n')
print(json.dumps(dict(status='PASS', source_sha256=digest(source), official_module=str(target),
    audit_addition=addition.decode().strip(), actual_jobs=3, failed_jobs=1, new_lean_lake_jobs=0)))
