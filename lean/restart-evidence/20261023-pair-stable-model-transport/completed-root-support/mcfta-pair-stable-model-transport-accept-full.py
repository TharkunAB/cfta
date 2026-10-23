import datetime
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path('/home/tritlo/Code/mcfta')
HERE = ROOT / 'lean/restart-evidence/20261023-pair-stable-model-transport'
AUDIT = Path('/tmp/mcfta-pair-stable-model-transport-public-audit')
def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

assert sha(AUDIT / 'review.json') == sys.argv[1]
independent = json.loads((AUDIT / 'review.json').read_text())
freeze = json.loads((AUDIT / 'FROZEN.json').read_text())
assert independent['status'] == 'CLEAR'
assert sha(AUDIT / 'pins.json') == freeze['pins_sha256']
pins = json.loads((AUDIT / 'pins.json').read_text())
if isinstance(pins, dict):
    pins = [dict(path=name, **pin) for name, pin in pins.items()]
for pin in pins:
    path = AUDIT / pin['path']
    assert path.stat().st_size == pin['bytes'] and sha(path) == pin['sha256'], path
name = 'SourceCurrentSameSymbolEdgeModelTransport'
source = HERE / (name + '.lean')
assert sha(source) == '69a294d6519b9029480175702b8025b1b1a32a1d2328e3c24b6ad0916972610f'
assert len(source.read_bytes().splitlines()) == 41
readback = json.loads((HERE / 'public-readback/pair-stable-model-transport-full-readback.json').read_text())
head, = readback['heads']
checked = HERE / 'public-readback/pair-stable-model-transport-rebase-public-type.txt'
printed = HERE / 'public-readback/pair-stable-model-transport-rebase-printed-public-type.txt'
assert checked.read_bytes() == printed.read_bytes() and sha(checked) == '4eaaf82ba9e58cac4adf879eb745c56dd08e8a6f01aae675c1b281b8553c97f2'
assert len(checked.read_bytes().splitlines()) == 209 and checked.read_bytes().count(b'\n') == 208
assert head['actual_axioms'] == ['Quot.sound', 'propext']
for filename, pin in readback['retained_slices'].items():
    path = HERE / 'public-readback' / filename
    assert path.stat().st_size == pin['bytes'] and sha(path) == pin['sha256']
raw = HERE / 'pair-stable-model-transport-public-1.log'
assert raw.stat().st_size == 651018 and sha(raw) == readback['log_sha256'] == '60e482e706203117cc772e4ac8a2b0040d1463474ad9015c7d40b98ce268a230'
assert (HERE / 'pair-stable-model-transport-strict-1.log').read_bytes() == b''
subprocess.run(['/usr/bin/python3', str(HERE / 'archive-extra.py'), str(AUDIT), 'public-audit'], check=True)
report = dict(status='ROOT_ACCEPTED_FOR_OFFICIAL_INSTALL_AND_AUDIT',
    observed_at=datetime.datetime.now().astimezone().isoformat(), source_sha256=sha(source), source_lines=41,
    public_heads=[head['head']], complete_public_type_root_review='CLEAR', independent_complete_public_type_review='CLEAR',
    root_read_complete_public_types=True, four_private_markers_and_all_helpers_absent_from_type=True,
    types_sha256={'rebase': sha(checked)}, full_raw_sha256=sha(raw), actual_axioms_by_head={'rebase': head['actual_axioms']},
    body_retained_and_programmatically_checked=True, whole_body_manual_read_claimed=False,
    root_printed_type_lexical_identity_verified=True, raw_type_byte_identity_by_head={'rebase': True},
    root_printed_type_byte_identity_verified=True, independent_review='public-audit/review.json',
    independent_review_sha256=sha(AUDIT / 'review.json'), complete_checked_type_lines=209,
    complete_checked_type_bytes=15378, root_manual_read_scope='All209 logical checked TYPE lines and41 ordinary source lines. Printed TYPE and complete BODY checked programmatically. No whole BODY manual read claim.')
for key in ['same_populated_wrapper_model_transport_derived', 'both_edge_law_fields_and_ranks_retained', 'old_captured_request_admission_explicit']:
    report[key] = True
for key in ['actual_admission_producer_claimed', 'native_covered_claimed', 'generated_root_composition_claimed',
    'new_source_room_claimed', 'word_ranges_claimed', 'public_pass_claimed', 'haskell_refinement_claimed',
    'whole_goal_complete', 'future_success_premise']:
    report[key] = False
(HERE / 'root-full-review.json').write_text(json.dumps(report, indent=2) + '\n')
target = ROOT / 'lean/MicroCFTA' / (name + '.lean')
aggregate = ROOT / 'lean/MicroCFTA/Audit.lean'
original = (HERE / 'original-sources/Audit.original.lean.txt').read_bytes()
assert not target.exists() and aggregate.read_bytes() == original
addition = ('import MicroCFTA.' + name + '\n').encode()
assert addition not in original
offset = original.index(b'/-!')
target.write_bytes(source.read_bytes())
aggregate.write_bytes(original[:offset] + addition + original[offset:])
assert aggregate.read_bytes().replace(addition, b'', 1) == original
with (HERE / 'current-progress.md').open('a') as output:
    output.write('\n## Complete public statement accepted\n\nThe first strict check passes with an empty log. The sole FULL passes.\nRoot and independent reviewers read all209 public TYPE lines.\nChecked and printed TYPE bytes match. Actual axioms are propext and Quot.sound only.\nThe exact41-line module and one inverse Audit import are installed.\nThe aggregate Audit remains pending. The whole goal stays ACTIVE.\n')
print(json.dumps(dict(status='PASS', official_module=str(target), actual_jobs=2, failed_jobs=0, new_lean_lake_jobs=0)))
