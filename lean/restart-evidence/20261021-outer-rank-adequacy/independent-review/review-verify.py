"""Verify independent review metadata without compiling or evaluating C."""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sys

HERE = Path(__file__).resolve().parent
parser = argparse.ArgumentParser()
parser.add_argument('--root', type=Path, required=True)
parser.add_argument('--live', action='store_true')
args = parser.parse_args()
def load(name):
    return json.loads((HERE / name).read_text())
def check(path, pin):
    data = path.read_bytes()
    assert len(data) == pin['bytes'], str(path)
    assert hashlib.sha256(data).hexdigest() == pin['sha256'], str(path)
def relative(name):
    path = Path(name)
    assert not path.is_absolute() and '..' not in path.parts
    return path
manifest = load('review-manifest.json')
selected = load('review-selection.json')
assert manifest['finalized'] and selected['finalized']
for pin in manifest['files']:
    check(HERE / relative(pin['path']), pin)
owner_pins = load('review-owner-pins.json')
assert owner_pins['finalized']
for name, pin in owner_pins['files'].items():
    check(HERE / 'owner' / relative(name), pin)
index = load('review-source-index.json')
owner_index = load('owner/source-index.json')
assert index['all_ranges_reviewed'] and index['sources'] == owner_index['sources']
assert len(index['sources']) == 32
assert sum(len(s['reviewed_ranges']) for s in index['sources']) == 45
assert all(s['authority'] == 'root' for s in index['sources'])
for pin in index['sources']:
    if args.live:
        check(args.root / relative(pin['path']), pin)
owner_selected = load('owner/outer-rank-adequacy-selection.json')
assert selected['selected_source_sha256'] == owner_selected['source_sha256']
assert selected['corrected_header_sha256'] == owner_selected['exact_header_sha256']
assert selected['actual_author_jobs'] == owner_selected['actual_lean_jobs'] == 9
assert selected['nonzero_author_jobs'] == owner_selected['failed_jobs'] == 6
assert selected['warning_bearing_author_jobs'] == 2
assert selected['warned_zero_author_jobs'] == 1 and selected['clean_zero_author_jobs'] == 2
assert selected['global_root_reported_jobs'] == 11
assert selected['root_reported_audit'] == {'jobs': 3617, 'dependencies': 75216}
assert selected['personally_read_complete_source_and_deltas']
assert selected['personally_read_checked_type_lines'] == 308
assert not selected['personally_read_entire_expanded_proof_body']
assert selected['authored_foundations_disclosed'] and not selected['material_issues']
assert selected['reviewer_lean_jobs'] == selected['reviewer_capped_jobs'] == 0
assert selected['reviewer_runtime_jobs'] == selected['reviewer_official_edits'] == 0
readback = load('owner/outer-rank-adequacy-full-public-readback.json')
assert readback == load('full-readback/owner-readback.json')
assert readback['log_bytes'] == 30964532
head = readback['heads'][0]
assert head['normalized_type_characters'] == 14616
assert head['body_characters'] == 30914096
assert head['actual_axioms'] == ['Classical.choice', 'Quot.sound', 'propext']
assert head['check_print_type_identity'] and not head['private_public_type_names']
assert (HERE / 'full-readback/checked-public-type.txt').read_bytes() == (HERE / 'owner/outer-rank-adequacy-public-type.txt').read_bytes()
command = [sys.executable, str(HERE / 'owner/outer-rank-adequacy-verify.py'), '--root', str(args.root)]
if args.live:
    command.append('--live')
result = json.loads(subprocess.check_output(command, text=True, cwd='/'))
assert result['status'] == 'PASS' and result['local_pins'] == 276
assert result['root_pins'] == 32 and result['source_ranges'] == 45
assert result['actual_lean_jobs'] == 9 and result['nonzero_exit_jobs'] == 6
assert result['new_verification_proof_jobs'] == 0
print(json.dumps(dict(status='PASS', live=args.live, finalized=True, local_pins=len(manifest['files']), copied_owner_local_pins=276, root_pins=32, source_ranges=45, actual_author_lean_jobs=9, nonzero_author_jobs=6, warning_bearing_author_jobs=2, reviewer_lean_jobs=0, reviewer_capped_jobs=0, reviewer_runtime_jobs=0), indent=2))
