from pathlib import Path
import datetime
import hashlib
import json

ROOT = Path('/home/tritlo/Code/mcfta')
BASE = ROOT / 'lean/restart-evidence'
WORK = BASE / '20261118-source-inventory-local-coverage-work'
CONTROL = BASE / '20261118-source-inventory-local-coverage-source-commit-control-draft'
PUBLICATION = BASE / '20261118-source-inventory-local-coverage-publication-control-draft'
RUN = BASE / '20261118-source-inventory-local-coverage-publication'
SHA = lambda data: hashlib.sha256(data).hexdigest()
read = lambda path: json.loads(path.read_text())
write = lambda path, data: path.write_text(json.dumps(data, indent=2, sort_keys=True) + '\n')

assert Path(__file__).resolve().parent == WORK
assert not (CONTROL / 'MANIFEST.json').exists()
assert (CONTROL / 'STATUS.txt').read_text().startswith('OPEN')
assert SHA((CONTROL / 'commit-source.py').read_bytes()) == \
    '68dea5112b336cc567e836d69fb95be2997212c04d8a150eb2c34dc0c67ea011'
actual = read(WORK / 'PUBLICATION-ACTUAL-RUN.json')
verified = read(WORK / 'PUBLICATION-VERIFIED.json')
assert actual['actual_session'] == verified['actual_session'] == 17653
assert actual['actual_terminal'] and verified['actual_terminal']
assert actual['actual_terminal_exit'] == verified['actual_terminal_exit'] == 0
assert actual['actual_tool_terminal_return_recovered']
assert verified['all_five_gates_passed'] and verified['proof_credit']
assert actual['control_manifest_sha256'] == SHA((PUBLICATION / 'MANIFEST.json').read_bytes())
assert actual['preparer_sha256'] == SHA((PUBLICATION / 'prepare-publication.py').read_bytes())
checked = read(RUN / 'checked.json')
assert checked == read(RUN / 'results.json') and checked['checks'] == verified['checks']
assert SHA((RUN / 'checked.json').read_bytes()) == verified['checked_sha256']
assert SHA((RUN / 'results.json').read_bytes()) == verified['results_sha256']
assert checked['audited_theorems'] == verified['audited_theorems']
assert [item['total_axiom_reports'] for item in checked['checks']] == [751, 4, 346, 751, 751]
assert [item['declaration_checks'] for item in checked['checks']] == [0, 0, 0, 0, 0]
assert all(item['exit'] == 0 and not item['diagnostics'] and not item['sorryAx']
           and not item['nonstandard_axioms'] for item in checked['checks'])
pins = read(RUN / 'source-pins.json')
assert len(pins) == verified['pins_independently_reverified'] == 11467
assert SHA((RUN / 'source-pins.json').read_bytes()) == verified['source_pins_sha256']
for name, digest in pins.items():
    assert SHA((ROOT / name).read_bytes()) == digest, name
for name in ['EXPECTED-STAGE.json', 'PRIVATE-CHECK.json']:
    (CONTROL / name).write_bytes((PUBLICATION / name).read_bytes())
for name in ['PUBLICATION-VERIFIED.json', 'PUBLICATION-ACTUAL-RUN.json',
             'REPAIR-CHECK-VERIFIED.json', 'REPAIR-CHECK-ACTUAL-RUN.json',
             'STAGING-ACTUAL-RUN.json']:
    (CONTROL / ('FINAL-' + name)).write_bytes((WORK / name).read_bytes())
write(CONTROL / 'FINAL-FREEZE-GATES.json', {
    'status': 'FINAL PRIVATE, STAGING AND PUBLICATION PASS / SOURCE COMMIT NOT EXECUTED',
    'private_final_pass': True, 'staging_final_pass': True, 'publication_final_pass': True,
    'actual_private_session': 88325, 'actual_staging_session': 71156,
    'actual_publication_session': 17653, 'source_commit_final_pass': None,
    'audited_theorems': checked['audited_theorems'], 'checkpoint_executed': False,
})
comparison = read(CONTROL / 'REPAIR-REBINDING-COMPARISON.json')
comparison.update(status='FINAL PUBLICATION PASS / SOURCE COMMIT NOT EXECUTED',
                  actual_repaired_private_success=True)
write(CONTROL / 'REPAIR-REBINDING-COMPARISON.json', comparison)
for path in RUN.rglob('*'):
    if path.is_file():
        pins[str(path.relative_to(ROOT))] = SHA(path.read_bytes())
for name in ['PUBLICATION-VERIFIED.json', 'PUBLICATION-ACTUAL-RUN.json',
             'NORMAL-CONTROLS-ROOT-REVIEW.json', 'CHECKPOINT-ENGINES-ROOT-REVIEW.json']:
    path = WORK / name
    pins[str(path.relative_to(ROOT))] = SHA(path.read_bytes())
write(CONTROL / 'SOURCE-PINS.json', pins)
(CONTROL / 'STATUS.txt').write_text('FROZEN SOURCE COMMIT CONTROLLER / NOT EXECUTED\n')
manifest = {
    'status': 'FROZEN SOURCE COMMIT CONTROLLER / NOT EXECUTED',
    'Root_frozen_at': datetime.datetime.now().astimezone().isoformat(),
    'all_final_receipts_bound_before_freeze': True,
    'files': {str(path.relative_to(CONTROL)): {
        'sha256': SHA(path.read_bytes()), 'bytes': path.stat().st_size,
    } for path in sorted(CONTROL.rglob('*')) if path.is_file()},
}
write(CONTROL / 'MANIFEST.json', manifest)
(WORK / 'commit-source.py').write_bytes((CONTROL / 'commit-source.py').read_bytes())
print(json.dumps({'manifest_sha256': SHA((CONTROL / 'MANIFEST.json').read_bytes()),
                  'input_pins': len(pins), 'payloads': len(manifest['files'])}))
