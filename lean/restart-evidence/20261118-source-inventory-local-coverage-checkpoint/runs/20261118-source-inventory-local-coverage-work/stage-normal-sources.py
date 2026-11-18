from pathlib import Path
import datetime
import json
ROOT = Path('/home/tritlo/Code/mcfta')
BASE = ROOT/'lean/restart-evidence'
CONTROL = BASE/'20261118-source-inventory-local-coverage-staging-control-draft'
WORK = BASE/'20261118-source-inventory-local-coverage-work'
assert (CONTROL/'STATUS.txt').read_text().startswith('FROZEN'),'OPEN control; do not execute.'
assert Path(__file__).resolve().parent == WORK.resolve() and Path(__file__).read_bytes() == (CONTROL/'stage-normal-sources.py').read_bytes()
assert not (WORK/'SOURCES-NORMAL-STAGING.json').exists()
exec(compile((CONTROL/'validate-inputs.py.txt').read_text(),str(CONTROL/'validate-inputs.py.txt'),'exec'))
stage,baseline,components,raws,probes,audit,verified,prior,classification = preflight(CONTROL)
assert all(not (ROOT/e['source_path']).exists() for e in components if e['new_module'])
expected = read(CONTROL/'EXPECTED-NORMAL-SOURCE-PINS.json')
assert len(expected) == 6294
for name,record in {**baseline['sources'],**baseline['toolchain']}.items():
    wanted = SHA(audit) if name == AUDIT else (raws[components[0]['module']] if name == OWNER else None)
    assert expected[name] == (SHA(wanted) if isinstance(wanted,bytes) else wanted if wanted is not None else record['sha256'])
for component in components:
    assert expected[component['source_path']] == SHA(raws[component['module']])
assert all(not (ROOT/path).exists() for path in stage['baseline_overrides'].values())
preflight_pins = {str(path.relative_to(ROOT)):SHA(path.read_bytes()) for path in bound}
# Root writes exactly three selected modules and Audit after every read-only gate passes.
for name,path in stage['baseline_overrides'].items():
    (ROOT/path).write_bytes((ROOT/name).read_bytes())
for component in components:
    (ROOT/component['source_path']).write_bytes(raws[component['module']])
(ROOT/AUDIT).write_bytes(audit)
for name,digest in expected.items():
    assert SHA((ROOT/name).read_bytes()) == digest,name
for name,digest in preflight_pins.items():
    assert SHA((ROOT/stage['baseline_overrides'].get(name,name)).read_bytes()) == digest,name
assert len(list((ROOT/'lean/MicroCFTA').glob('*.lean'))) == 6290
(WORK/'NORMAL-SOURCE-PINS.json').write_bytes((CONTROL/'EXPECTED-NORMAL-SOURCE-PINS.json').read_bytes())
for name in ['IMPORTS.lean.txt','PUBLIC-PROBES.lean.txt']:
    (WORK/name).write_bytes((CONTROL/name).read_bytes())
result = dict(stage)
result.update(status='SOURCE_NORMAL_STAGING_COMPLETED',staged_at=datetime.datetime.now().astimezone().isoformat(),normal_Source_changed=True,published=False,actual_private_session=verified['actual_session'],actual_private_sessions=[verified['actual_session']],fresh_classification=classification,normal_source_pins_sha256=SHA((WORK/'NORMAL-SOURCE-PINS.json').read_bytes()))
(WORK/'SOURCES-NORMAL-STAGING.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
