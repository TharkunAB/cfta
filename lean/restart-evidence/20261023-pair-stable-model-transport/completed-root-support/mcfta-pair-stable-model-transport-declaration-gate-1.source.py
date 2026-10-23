import datetime
import hashlib
import json
import subprocess
from pathlib import Path

ROOT = Path('/home/tritlo/Code/mcfta')
HERE = ROOT / 'lean/restart-evidence/20261023-pair-stable-model-transport'
SOURCE = Path('/tmp/mcfta-pair-stable-model-transport-signature')
AUDIT = Path('/tmp/mcfta-pair-stable-model-transport-signature-audit')

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

assert sha(SOURCE / 'pins.json') == '395f70e03e9117a98e89fd828b180b72faf5de7cec9dd5e51b2419f811c1e67f'
assert sha(SOURCE / 'FROZEN.json') == 'a743cc49ae9628d60a6ce0e9fe9c7e68f9941b192f0b33f14b00b953c27b2e46'
pins = json.loads((SOURCE / 'pins.json').read_text())
assert isinstance(pins, list) and len(pins) == 43
for pin in pins:
    path = SOURCE / pin['path']
    assert path.stat().st_size == pin['bytes'] and sha(path) == pin['sha256'], path
index = json.loads((SOURCE / 'source-index.json').read_text())
assert len(index['sources']) == 8
cuts = lines = 0
for entry in index['sources']:
    path = ROOT / entry['path']
    data = path.read_bytes()
    assert data == (SOURCE / entry['snapshot']).read_bytes()
    assert len(data) == entry['bytes'] and sha(path) == entry['sha256']
    assert len(data.splitlines()) == entry['lines']
    for cut in entry['cuts']:
        snapshot = SOURCE / cut['snapshot']
        assert snapshot.read_bytes() == b''.join(data.splitlines(True)[cut['start'] - 1:cut['end']])
        assert snapshot.stat().st_size == cut['bytes'] and sha(snapshot) == cut['sha256']
        cuts += 1
        lines += cut['end'] - cut['start'] + 1
assert cuts == 14
imports = json.loads((SOURCE / 'import-paths.json').read_text())
for chain in imports['existing_api_paths'].values():
    assert chain[0] in imports['direct_imports']
    for first, second in zip(chain, chain[1:]):
        path = ROOT / 'lean' / Path(*first.split('.')).with_suffix('.lean')
        assert 'import ' + second in path.read_text().splitlines(), (first, second)
contracts = json.loads((SOURCE / 'contracts.json').read_text())
assert list(contracts) == ['context.lean.txt', 'public-header.lean.txt']
assert sha(SOURCE / 'contracts.json') == '33dfa8ec3d82e3b535e586dd48df20ad8590d8fefce7699b6cf5b1c604ac3965'
for name, pin in contracts.items():
    path = SOURCE / name
    assert sha(path) == pin['sha256'] and len(path.read_bytes().splitlines()) == pin['lines']
shape = json.loads((SOURCE / 'declaration-shape.json').read_text())
assert shape['public_theorems'] == ['rebase']
assert not any(shape[key] for key in ['private_declarations', 'new_definitions', 'local_type_fragments', 'local_induction'])
assert json.loads((SOURCE / 'budget.json').read_text())['hard_stop_total_ordinary_lines'] == 120
assert (ROOT / 'lean/MicroCFTA/Audit.lean').read_bytes() == (HERE / 'original-sources/Audit.original.lean.txt').read_bytes()
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip() == '0d03a28e82f9f3d0b5dfbba16bc919fb16c422cb'
assert (AUDIT / 'FROZEN.json').exists()
audit_freeze = json.loads((AUDIT / 'FROZEN.json').read_text())
assert sha(AUDIT / 'FROZEN.json') == '9589d78205dd69513f5d51f87d07a9c138ed368915ae4f2ea7d5ebcae925aab7'
assert audit_freeze['status'] == 'FINAL_FROZEN_INDEPENDENT_DECLARATION_SOURCE_CLEAR'
assert sha(AUDIT / 'pins.json') == '3144794739af493fa9076a5fc11b16c6937783790e320c426acf4dd10c722b24'
audit_review = json.loads((AUDIT / 'review.json').read_text())
assert audit_review['status'] == 'CLEAR' and audit_review['blockers'] == []
assert sha(AUDIT / 'review.json') == audit_freeze['review_json_sha256']
assert sha(AUDIT / 'review.md') == audit_freeze['review_md_sha256']
audit_pins = json.loads((AUDIT / 'pins.json').read_text())
if isinstance(audit_pins, dict):
    audit_pins = [dict(path=name, **pin) for name, pin in audit_pins.items()]
for pin in audit_pins:
    path = AUDIT / pin['path']
    assert path.stat().st_size == pin['bytes'] and sha(path) == pin['sha256'], path
for source, name in [(SOURCE, 'signature-plan'), (AUDIT, 'signature-audit')]:
    subprocess.run(['/usr/bin/python3', str(HERE / 'archive-extra.py'), str(source), name], check=True)
report = dict(status='ROOT_DECLARATION_REVIEW_CLEAR',
    observed_at=datetime.datetime.now().astimezone().isoformat(),
    module=shape['module'], public_names=['rebase'], private_names=[], local_names=[], local_induction=None,
    source_target=[50, 90], source_hard_stop=120, contract_sha256=sha(SOURCE / 'contracts.json'),
    root_whole_exact_declarations_read=True, root_source_identities=8, root_source_cuts=cuts,
    root_source_cut_lines=lines, independent_source_review='CLEAR',
    independent_freeze_sha256=sha(AUDIT / 'FROZEN.json'), independent_pins_sha256=sha(AUDIT / 'pins.json'),
    same_literal_populated_wrapper=True, both_sound_and_bounded_complete_retained=True,
    genuine_old_captured_canonical_request_admission_explicit=True, new_result_law_premise=False,
    body_proposal_authorized=True, compiler_authorized=False, whole_goal_complete=False)
(HERE / 'root-declaration-review.json').write_text(json.dumps(report, indent=2) + '\n')
with (HERE / 'current-progress.md').open('a') as output:
    output.write('\n## Exact declaration gate\n\nRoot and independent declaration reviews pass.\nThe one public rebase theorem can receive a body proposal.\nNo private helper, new definition, local typed obligation or induction is authorized.\nThe same literal populated Wrapper retains both language and rank laws.\nGenuine old admission applies to actual returned canonical captured requests.\nThe source has a 120-line hard stop. No compiler command is authorized yet.\nThe whole formalization goal remains ACTIVE.\n')
print(json.dumps(report))
