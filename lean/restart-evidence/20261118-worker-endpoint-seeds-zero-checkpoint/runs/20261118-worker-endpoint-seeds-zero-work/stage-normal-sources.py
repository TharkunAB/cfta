from pathlib import Path
import datetime
import hashlib
import json

ROOT = Path('/home/tritlo/Code/mcfta')
BASE = ROOT/'lean/restart-evidence'
CONTROL = BASE/'20261118-worker-endpoint-seeds-zero-staging-control-draft'
WORK = BASE/'20261118-worker-endpoint-seeds-zero-work'
assert (CONTROL/'STATUS.txt').read_text().startswith('FROZEN'), 'OPEN control; do not execute.'
assert Path(__file__).resolve().parent == WORK.resolve()
assert Path(__file__).read_bytes() == (CONTROL/'stage-normal-sources.py').read_bytes()
assert not (WORK/'SOURCES-NORMAL-STAGING.json').exists()
exec(compile((CONTROL/'validate-inputs.py.txt').read_text(),str(CONTROL/'validate-inputs.py.txt'),'exec'))
baseline,component,raw,probes,leaf,zero,prior,classification = preflight(CONTROL)
stage = read(CONTROL/'EXPECTED-STAGE.json')
assert stage['exact_Source_write_paths'] == [OWNER]
assert stage['baseline_overrides'] == {OWNER:str((WORK/'SharedEagerReservation-BEFORE.lean.txt').relative_to(ROOT))}
assert stage['new_public_theorems'] == 0 and stage['new_private_theorems'] == 2
assert stage['new_private_Prop_definitions'] == stage['definition_checks'] == 3
assert stage['definition_axiom_credit'] == 0 and stage['Audit_changed'] is False
assert (stage['source_files'],stage['audit_imports'],stage['audit_reports'],stage['independent_reports']) == (6286,5286,744,339)
assert (stage['inherited_reports'],stage['fresh_private_reports'],stage['combined_reports']) == (538,2,540)
expected = read(CONTROL/'EXPECTED-NORMAL-SOURCE-PINS.json')
assert len(expected) == 6290
for name,record in {**baseline['sources'],**baseline['toolchain']}.items():
    assert expected[name] == (SHA(raw) if name == OWNER else record['sha256'])
snapshot = ROOT/stage['baseline_overrides'][OWNER]
assert not snapshot.exists() and not (WORK/'NORMAL-SOURCE-PINS.json').exists()
preflight_pins = {str(path.relative_to(ROOT)):SHA(path.read_bytes()) for path in bound}
for name,digest in preflight_pins.items():
    assert SHA((ROOT/name).read_bytes()) == digest,name
old = (ROOT/OWNER).read_bytes()
# Root performs one normal Source write after every gate passes. Audit is read only.
snapshot.write_bytes(old)
(ROOT/OWNER).write_bytes(raw)
for name,digest in expected.items():
    assert SHA((ROOT/name).read_bytes()) == digest,name
for name,digest in preflight_pins.items():
    assert SHA((ROOT/stage['baseline_overrides'].get(name,name)).read_bytes()) == digest,name
assert len(list((ROOT/'lean/MicroCFTA').glob('*.lean'))) == 6286
(WORK/'NORMAL-SOURCE-PINS.json').write_bytes((CONTROL/'EXPECTED-NORMAL-SOURCE-PINS.json').read_bytes())
(WORK/'STRICT-OWNER-PROBES.lean.txt').write_bytes(probes)
actual = dict(stage)
actual.update(status='SOURCE_NORMAL_STAGING_COMPLETED',staged_at=datetime.datetime.now().astimezone().isoformat(),
    actual_private_sessions=[leaf[0]['actual_session'],zero[0]['actual_session']],normal_Source_changed=True,published=False,
    actual_Source_files=6286,actual_audit_imports=5286,actual_audit_reports=744,
    prior_source_checkpoint_push_verified=True,fresh_classification=classification,
    normal_source_pins_sha256=SHA((WORK/'NORMAL-SOURCE-PINS.json').read_bytes()))
(WORK/'SOURCES-NORMAL-STAGING.json').write_text(json.dumps(actual,indent=2)+'\n')
print(json.dumps(actual,indent=2))
