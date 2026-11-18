from pathlib import Path
import ast
import datetime
import hashlib
import json

ROOT = Path('/home/tritlo/Code/mcfta')
BASE = ROOT / 'lean/restart-evidence'
WORK = BASE / '20261118-source-inventory-local-coverage-work'
CONTROL = BASE / '20261118-source-inventory-local-coverage-staging-control-draft'
RUN = BASE / '20261118-source-inventory-local-coverage-repair-check'
SHA = lambda data: hashlib.sha256(data).hexdigest()
read = lambda path: json.loads(path.read_text())
write = lambda path, data: path.write_text(json.dumps(data, indent=2, sort_keys=True) + '\n')

assert Path(__file__).resolve().parent == WORK
assert not (CONTROL / 'MANIFEST.json').exists()
assert (CONTROL / 'STATUS.txt').read_text().startswith('OPEN')
verified = read(WORK / 'REPAIR-CHECK-VERIFIED.json')
actual = read(WORK / 'REPAIR-CHECK-ACTUAL-RUN.json')
assert verified['actual_session'] == actual['actual_session'] == 88325
assert verified['actual_terminal'] and actual['actual_terminal']
assert verified['actual_terminal_exit'] == actual['actual_terminal_exit'] == 0
assert verified['actual_tool_terminal_return_recovered']
assert verified['proof_credit'] and not verified['normal_Source_changed']
checked = read(RUN / 'checked.json')
assert checked == read(RUN / 'results.json')
assert SHA((RUN / 'checked.json').read_bytes()) == verified['checked_sha256']
assert SHA((RUN / 'results.json').read_bytes()) == verified['results_sha256']
assert checked['checks'] == verified['checks']
assert [item['total_axiom_reports'] for item in checked['checks']] == [2, 1, 1]
assert all(item['exit'] == 0 and not item['diagnostics'] and not item['sorryAx']
           and not item['nonstandard_axioms'] for item in checked['checks'])
pins = read(RUN / 'source-pins.json')
assert len(pins) == verified['pins_independently_reverified'] == 11370
assert SHA((RUN / 'source-pins.json').read_bytes()) == verified['source_pins_sha256']
for name, digest in pins.items():
    assert SHA((ROOT / name).read_bytes()) == digest, name
for name, digest in {
    'stage-normal-sources.py': 'f1afa17230cad1531617e43aefe8da84645d374987560ce7826842ea7a1d1a54',
    'validate-inputs.py.txt': 'ead8d7a619ba7bab93fcf4f8711e44af7ce6dd27e75eecd48b9160d6a7044c7f',
}.items():
    assert SHA((CONTROL / name).read_bytes()) == digest, name
    ast.parse((CONTROL / name).read_text())

private = read(CONTROL / 'PRIVATE-CHECK.json')
private.update(status='FINAL REPAIRED WHOLE PRIVATE CHECK PASS',
    control_manifest_sha256=actual['control_manifest_sha256'],
    actual_session=88325,
    verified_receipt=str((WORK / 'REPAIR-CHECK-VERIFIED.json').relative_to(ROOT)),
    actual_receipt=str((WORK / 'REPAIR-CHECK-ACTUAL-RUN.json').relative_to(ROOT)),
    receipt_names_status='FINAL ROOT RECEIPT NAMES',
    actual_terminal=True, actual_success=True, actual_terminal_exit=0,
    runtime_input_pins=11370)
write(CONTROL / 'PRIVATE-CHECK.json', private)
stage = read(CONTROL / 'EXPECTED-STAGE.json')
stage.update(status='FROZEN STAGING CANDIDATE / PRIVATE CHECK PASSED / NOT STAGED',
             actual_private_session=88325, selected_repair_pending=False)
write(CONTROL / 'EXPECTED-STAGE.json', stage)
for name in ['REPAIR-CHECK-VERIFIED.json', 'REPAIR-CHECK-ACTUAL-RUN.json',
             'FIRST-FAILED-CHECK-VERIFIED.json', 'ACTUAL-RUN.json']:
    (CONTROL / ('FINAL-' + name)).write_bytes((WORK / name).read_bytes())
write(CONTROL / 'FINAL-FREEZE-GATES.json', {
    'status': 'FINAL PRIVATE PASS / NORMAL STAGING NOT EXECUTED',
    'actual_private_session': 88325, 'actual_private_terminal_exit': 0,
    'actual_private_pins': 11370, 'private_final_pass': True,
    'component_axiom_reports': [2, 1, 1], 'component_definition_checks': [0, 0, 0],
    'first_failed47632_whole_batch_credit': 0, 'normal_Source_staged': False,
    'publication_pending': True, 'full_producer334c_proved': False,
})
comparison = read(CONTROL / 'REPAIR-REBINDING-COMPARISON.json')
comparison.update(status='FINAL REPAIR PRIVATE PASS / STAGING NOT EXECUTED',
                  actual_repaired_private_success=True)
write(CONTROL / 'REPAIR-REBINDING-COMPARISON.json', comparison)
for path in RUN.rglob('*'):
    if path.is_file():
        pins[str(path.relative_to(ROOT))] = SHA(path.read_bytes())
for name in ['REPAIR-CHECK-VERIFIED.json', 'REPAIR-CHECK-ACTUAL-RUN.json',
             'REPAIR-CONTROLLER-ROOT-REVIEW.json']:
    path = WORK / name
    pins[str(path.relative_to(ROOT))] = SHA(path.read_bytes())
write(CONTROL / 'SOURCE-PINS.json', pins)
(CONTROL / 'STATUS.txt').write_text('FROZEN STAGING CONTROLLER / NOT EXECUTED\n')
manifest = {
    'status': 'FROZEN STAGING CONTROLLER / NOT EXECUTED',
    'Root_frozen_at': datetime.datetime.now().astimezone().isoformat(),
    'files': {str(path.relative_to(CONTROL)): {
        'sha256': SHA(path.read_bytes()), 'bytes': path.stat().st_size,
    } for path in sorted(CONTROL.rglob('*')) if path.is_file()},
}
write(CONTROL / 'MANIFEST.json', manifest)
(WORK / 'stage-normal-sources.py').write_bytes((CONTROL / 'stage-normal-sources.py').read_bytes())
print(json.dumps({'manifest_sha256': SHA((CONTROL / 'MANIFEST.json').read_bytes()),
                  'input_pins': len(pins), 'payloads': len(manifest['files'])}))
