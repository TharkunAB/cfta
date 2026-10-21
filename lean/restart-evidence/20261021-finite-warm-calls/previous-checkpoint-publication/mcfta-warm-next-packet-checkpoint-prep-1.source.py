import difflib
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
previous = HERE.parent / '20261021-warm-rank-grid'
templates = HERE / 'checkpoint-templates'
templates.mkdir()
pins = {}
def adapted(name, original, replacements):
    changed = original
    for old, new in replacements:
        assert old in changed, (name, old)
        changed = changed.replace(old, new)
    (templates / (name + '.original.py.txt')).write_text(original)
    (templates / (name + '.patch')).write_text(''.join(difflib.unified_diff(
        original.splitlines(True), changed.splitlines(True), fromfile=name+'.original', tofile=name)))
    assert not (HERE / name).exists()
    (HERE / name).write_text(changed)
    pins[name] = hashlib.sha256(changed.encode()).hexdigest()

adapted('verify-checkpoint.py', (previous / 'verify-checkpoint.py').read_text(), [
    ("report['actual_jobs'] == 8 and report['failed_jobs'] == 3", "report['actual_jobs'] == 3 and report['failed_jobs'] == 0"),
    ("report['source_jobs'] == 7", "report['source_jobs'] == 2"),
    ("report['selected_modules'] == 2", "report['selected_modules'] == 1"),
    ("report['audit_build_jobs'] == 3620", "report['audit_build_jobs'] == 3621"),
    ("report['audit_dependencies'] == 75252", "report['audit_dependencies'] == 75253"),
    ("preserved['baseline_files'] == 71517", "preserved['baseline_files'] == 72392"),
    ("len(selected) == 2", "len(selected) == 1")])
adapted('seal-checkpoint.py', (previous / 'seal-checkpoint.py').read_text(), [
    ('notes-current-finite-round-forecast.md', 'notes-current-warm-next-packet.md')])
adapted('verify-seal.py', (previous / 'verify-seal.py').read_text(), [])
adapted('final-publication.py', Path('/tmp/mcfta-warm-rank-grid-final-publication.py').read_text(), [
    ('mcfta-warm-rank-grid', 'mcfta-warm-next-packet'),
    ('20261021-warm-rank-grid', '20261021-warm-next-packet'),
    ('99f2b2f9b63122539d8edb1eee5ac4cffa62ee6e', '0e0d372f5f42837c838f4beb6e4c5e2fcf24bb93'),
    ('93224c12e0336bdd80a5f51dd126ac93cd76bef0', '__H4_PROOF_COMMIT__'),
    ('notes-current-finite-round-forecast.md', 'notes-current-warm-next-packet.md'),
    ('Preserve finite-round forecast evidence and handoff', 'Preserve completed-return proof evidence and handoff')])
(HERE / 'checkpoint-preparation-pins.json').write_text(json.dumps(pins, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'source_only_preparation': True, 'publisher_proof_pin_pending': True, 'pins': pins}))
