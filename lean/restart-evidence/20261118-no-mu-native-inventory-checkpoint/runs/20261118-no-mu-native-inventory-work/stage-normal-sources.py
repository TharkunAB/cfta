from pathlib import Path
import datetime
import json
ROOT = Path('/home/tritlo/Code/mcfta')
BASE = ROOT/'lean/restart-evidence'
CONTROL = BASE/'20261118-no-mu-native-inventory-staging-control-draft'
WORK = BASE/'20261118-no-mu-native-inventory-work'
assert Path(__file__).resolve().parent == WORK and Path(__file__).read_bytes() == (CONTROL/'stage-normal-sources.py').read_bytes()
assert not (WORK/'SOURCES-NORMAL-STAGING.json').exists()
exec(compile((CONTROL/'validate-inputs.py.txt').read_text(),str(CONTROL/'validate-inputs.py.txt'),'exec'))
stage,baseline,component,raw,probe,audit,verified,prior,classification = preflight(CONTROL)
assert not (ROOT/component['source_path']).exists()
expected = read(CONTROL/'EXPECTED-NORMAL-SOURCE-PINS.json')
assert len(expected) == 6295
for name,record in {**baseline['sources'],**baseline['toolchain']}.items():
    assert expected[name] == (SHA(audit) if name == AUDIT else record['sha256'])
assert expected[component['source_path']] == SHA(raw)
assert all(not (ROOT/path).exists() for path in stage['baseline_overrides'].values())
before = {str(path.relative_to(ROOT)):SHA(path.read_bytes()) for path in bound}
# Root writes only the new leaf and Audit after all read-only gates pass.
for name,path in stage['baseline_overrides'].items():
    (ROOT/path).write_bytes((ROOT/name).read_bytes())
(ROOT/component['source_path']).write_bytes(raw)
(ROOT/AUDIT).write_bytes(audit)
for name,digest in expected.items():
    assert SHA((ROOT/name).read_bytes()) == digest,name
for name,digest in before.items():
    assert SHA((ROOT/stage['baseline_overrides'].get(name,name)).read_bytes()) == digest,name
assert len(list((ROOT/'lean/MicroCFTA').glob('*.lean'))) == 6291
(WORK/'NORMAL-SOURCE-PINS.json').write_bytes((CONTROL/'EXPECTED-NORMAL-SOURCE-PINS.json').read_bytes())
for name in ['IMPORTS.lean.txt','PUBLIC-PROBES.lean.txt']:
    (WORK/name).write_bytes((CONTROL/name).read_bytes())
result = dict(stage)
result.update(status='SOURCE_NORMAL_STAGING_COMPLETED',staged_at=datetime.datetime.now().astimezone().isoformat(),normal_Source_changed=True,published=False,actual_private_session=verified['actual_session'],actual_private_sessions=[verified['actual_session']],fresh_classification=classification,normal_source_pins_sha256=SHA((WORK/'NORMAL-SOURCE-PINS.json').read_bytes()))
(WORK/'SOURCES-NORMAL-STAGING.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
