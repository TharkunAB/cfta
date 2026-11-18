from pathlib import Path
import datetime
import json

ROOT = Path('/home/tritlo/Code/mcfta')
BASE = ROOT/'lean/restart-evidence'
CONTROL = BASE/'20261118-worker-current-seeds-staging-control-draft'
WORK = BASE/'20261118-worker-inner-selected-prefix-seeds-work'
assert (CONTROL/'STATUS.txt').read_text().startswith('FROZEN'), 'OPEN control; do not execute.'
assert Path(__file__).resolve().parent == WORK.resolve()
assert Path(__file__).read_bytes() == (CONTROL/'stage-normal-sources.py').read_bytes()
assert not (WORK/'SOURCES-NORMAL-STAGING.json').exists()
exec(compile((CONTROL/'validate-inputs.py.txt').read_text(),str(CONTROL/'validate-inputs.py.txt'),'exec'))
stage,baseline,component,raw,probes,bundles,prior,classification = preflight(CONTROL)
assert stage['exact_Source_write_paths'] == [OWNER] and set(stage['baseline_overrides']) == {OWNER}
assert (stage['new_public_theorems'],stage['new_private_theorems'],stage['new_private_helpers_transitive'],stage['new_definitions']) == (0,15,0,0)
assert stage['definition_checks'] == stage['definition_axiom_credit'] == 0 and not stage['Audit_changed']
assert (stage['source_files'],stage['audit_imports'],stage['audit_reports'],stage['independent_reports']) == (6286,5286,746,341)
assert (stage['inherited_reports'],stage['fresh_reports'],stage['combined_reports']) == (545,15,560)
expected = read(CONTROL/'EXPECTED-NORMAL-SOURCE-PINS.json')
assert len(expected) == 6290 and len(baseline['sources'])-1 == stage['old_other_Source_files_byte_exact'] == 6285
for name,record in {**baseline['sources'],**baseline['toolchain']}.items():
    assert expected[name] == (SHA(raw) if name == OWNER else record['sha256'])
snapshot = ROOT/stage['baseline_overrides'][OWNER]
assert not snapshot.exists() and not (WORK/'NORMAL-SOURCE-PINS.json').exists()
preflight_pins = {str(p.relative_to(ROOT)):SHA(p.read_bytes()) for p in bound}
for name,digest in preflight_pins.items():
    assert SHA((ROOT/name).read_bytes()) == digest,name
audit = (ROOT/'lean/MicroCFTA/Audit.lean').read_bytes()
# Root performs one normal owner write. Audit and all other Source bytes stay exact.
snapshot.write_bytes((ROOT/OWNER).read_bytes())
(ROOT/OWNER).write_bytes(raw)
for name,digest in expected.items():
    assert SHA((ROOT/name).read_bytes()) == digest,name
for name,digest in preflight_pins.items():
    assert SHA((ROOT/stage['baseline_overrides'].get(name,name)).read_bytes()) == digest,name
assert (ROOT/'lean/MicroCFTA/Audit.lean').read_bytes() == audit
(WORK/'NORMAL-SOURCE-PINS.json').write_bytes((CONTROL/'EXPECTED-NORMAL-SOURCE-PINS.json').read_bytes())
(WORK/'STRICT-OWNER-PROBES.lean.txt').write_bytes(probes)
result = dict(stage)
result.update(status='SOURCE_NORMAL_STAGING_COMPLETED',staged_at=datetime.datetime.now().astimezone().isoformat(),
    actual_private_sessions=[entry['verified']['actual_session'] for entry in bundles],normal_Source_changed=True,published=False,
    prior_source_checkpoint_push_verified=True,fresh_classification=classification,
    normal_source_pins_sha256=SHA((WORK/'NORMAL-SOURCE-PINS.json').read_bytes()))
(WORK/'SOURCES-NORMAL-STAGING.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
