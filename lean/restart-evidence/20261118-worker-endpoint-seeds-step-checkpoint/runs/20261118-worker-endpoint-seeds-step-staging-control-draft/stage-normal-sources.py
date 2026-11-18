from pathlib import Path
import datetime
import json

ROOT = Path('/home/tritlo/Code/mcfta')
BASE = ROOT/'lean/restart-evidence'
CONTROL = BASE/'20261118-worker-endpoint-seeds-step-staging-control-draft'
WORK = BASE/'20261118-worker-endpoint-seeds-step-work'
assert (CONTROL/'STATUS.txt').read_text().startswith('FROZEN'), 'OPEN control; do not execute.'
assert Path(__file__).resolve().parent == WORK.resolve()
assert Path(__file__).read_bytes() == (CONTROL/'stage-normal-sources.py').read_bytes()
assert not (WORK/'SOURCES-NORMAL-STAGING.json').exists()
exec(compile((CONTROL/'validate-inputs.py.txt').read_text(),str(CONTROL/'validate-inputs.py.txt'),'exec'))
stage,baseline,components,raw_sources,probes,public,verified,actual,prior,classification = preflight(CONTROL)
assert len(stage['exact_Source_write_paths']) == len(stage['baseline_overrides']) == 4
assert stage['new_public_theorems'] == 2 and stage['new_private_theorems'] == 6
assert stage['new_private_reported_laws'] == stage['new_private_helpers_transitive'] == 3
assert stage['new_definitions'] == stage['definition_checks'] == stage['definition_axiom_credit'] == 0
assert (stage['source_files'],stage['audit_imports'],stage['audit_reports'],stage['independent_reports']) == (6286,5286,746,341)
assert (stage['inherited_reports'],stage['fresh_reports'],stage['combined_reports']) == (540,5,545)
old_audit = (ROOT/'lean/MicroCFTA/Audit.lean').read_bytes()
assert old_audit == (CONTROL/'AUDIT-BEFORE.lean.txt').read_bytes()
new_audit = old_audit+b'\n'+public
assert len(new_audit) == stage['staged_audit_bytes'] == 436889 and SHA(new_audit) == stage['staged_audit_sha256']
assert len(re.findall(rb'^import ',new_audit,re.M)) == 5286 and new_audit.count(b'#print axioms ') == 746
assert new_audit[:436723] == old_audit and new_audit.count(b'#check ') == old_audit.count(b'#check ')
expected = read(CONTROL/'EXPECTED-NORMAL-SOURCE-PINS.json')
assert len(expected) == 6290
replacements = {c['source_path']:raw_sources[c['module']] for c in components}
replacements['lean/MicroCFTA/Audit.lean'] = new_audit
assert set(replacements) == set(stage['exact_Source_write_paths']) == set(stage['baseline_overrides'])
for name,record in {**baseline['sources'],**baseline['toolchain']}.items():
    assert expected[name] == (SHA(replacements[name]) if name in replacements else record['sha256'])
assert len(set(baseline['sources'])-set(replacements)) == 6282
assert all(not(ROOT/path).exists() for path in stage['baseline_overrides'].values())
assert not(WORK/'NORMAL-SOURCE-PINS.json').exists()
preflight_pins = {str(path.relative_to(ROOT)):SHA(path.read_bytes()) for path in bound}
for name,digest in preflight_pins.items():
    assert SHA((ROOT/name).read_bytes()) == digest,name
# Root writes exactly three existing owners and Audit after all read-only gates pass.
for name,snapshot in stage['baseline_overrides'].items():
    (ROOT/snapshot).write_bytes((ROOT/name).read_bytes())
for name,data in replacements.items():
    (ROOT/name).write_bytes(data)
for name,digest in expected.items():
    assert SHA((ROOT/name).read_bytes()) == digest,name
for name,digest in preflight_pins.items():
    assert SHA((ROOT/stage['baseline_overrides'].get(name,name)).read_bytes()) == digest,name
(WORK/'NORMAL-SOURCE-PINS.json').write_bytes((CONTROL/'EXPECTED-NORMAL-SOURCE-PINS.json').read_bytes())
(WORK/'PUBLIC-PROBES.lean.txt').write_bytes(public)
result = dict(stage)
result.update(status='SOURCE_NORMAL_STAGING_COMPLETED',staged_at=datetime.datetime.now().astimezone().isoformat(),
    actual_private_session=verified['actual_session'],normal_Source_changed=True,published=False,
    actual_Source_files=6286,actual_audit_imports=5286,actual_audit_reports=746,
    prior_source_checkpoint_push_verified=True,fresh_classification=classification,
    normal_source_pins_sha256=SHA((WORK/'NORMAL-SOURCE-PINS.json').read_bytes()))
(WORK/'SOURCES-NORMAL-STAGING.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
