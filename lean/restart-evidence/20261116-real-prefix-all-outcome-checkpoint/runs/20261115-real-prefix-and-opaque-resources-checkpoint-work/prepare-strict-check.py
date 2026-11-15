from pathlib import Path
import hashlib
import json
import shlex
import tempfile

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
all_cases = base / '20261116-current-real-prefix-all-outcome-explicit-selection-repair'
old = base / '20261116-current-real-prefix-all-outcome-typing-repair'
continuing = base / '20261116-current-real-prefix-continuing-normalization-repair'
for name in ['PUBLIC-HEADER.lean.txt', 'ZERO-HEADER.lean.txt', 'NONCONTINUING-HEADER.lean.txt',
             'PROBES.lean.txt', 'REMAINING-CONTINUING-TARGET-UNPROVED.lean.txt']:
    assert (all_cases / name).read_bytes() == (old / name).read_bytes(), name
assert (continuing / 'PUBLIC-HEADER.lean.txt').read_bytes() == (all_cases / 'REMAINING-CONTINUING-TARGET-UNPROVED.lean.txt').read_bytes()
specs = [(all_cases, 'SourcePruningEnumerationRealPrefixAllResources.lean',
    'e4adbc5f2aea392c04286c3e054899b28b47580ff20c31c7646dd9b9f27930ff', 'all-outcome'),
    (continuing, 'SourcePruningEnumerationRealPrefixContinuingResources.lean',
    'a4aa29f351942383e910ab40a9fd172e1eee6bef3b80f3601c9a2767a0dbf9f8', 'continuing')]
run = base / '20261116-native-real-resources-strict-normalization-check'
run.mkdir()
objects = Path(tempfile.mkdtemp(prefix='mcfta-real-prefix-proof-'))
(run / 'objects.json').write_text(json.dumps({'path':str(objects)}, indent=2) + '\n')
modules = set()
jobs = []
pins = list((root / 'lean/MicroCFTA').glob('*.lean'))
pins += [root / p for p in ['shell.nix', 'lean/lean-toolchain', 'lean/lakefile.toml', 'lean/lake-manifest.json']]
pins.append(Path(__file__))
for index, (folder, name, digest, label) in enumerate(specs):
    raw, probes = folder / name, folder / 'PROBES.lean.txt'
    assert hashlib.sha256(raw.read_bytes()).hexdigest() == digest
    source = run / ('source-' + str(index)) / 'MicroCFTA' / name
    source.parent.mkdir(parents=True)
    source.write_bytes(raw.read_bytes() + b'\n' + probes.read_bytes())
    modules.update(line.split()[1] for line in raw.read_text().splitlines() if line.startswith('import '))
    command = 'exec lake env lean -j1 -DwarningAsError=true -R ' + shlex.quote(str(source.parent.parent))
    command += ' -o ' + shlex.quote(str(objects / (label + '.olean'))) + ' ' + shlex.quote(str(source))
    jobs.append((label, command, probes.read_text().count('#print axioms ')))
    pins += [raw, probes, source]
jobs.insert(0, ('public-dependencies', 'exec lake build ' + ' '.join(map(shlex.quote, sorted(modules))), 0))
template = (base / '20261115-native-open-binder-helper-dependencies/check.py').read_text()
driver = template[:template.index('run("public-dependency"')]
driver += 'jobs = ' + repr(jobs) + '''
for name, command, count in jobs:
    try:
        run(name, command, count)
    except AssertionError:
        pass
assert all(item['exit'] == 0 and not item['nonstandard_axioms'] for item in checks)
(runtime/'checked.json').write_text(json.dumps({'checks':checks,'source_pins_unchanged':True,
    'all_real_prefix_tag_resources_at_original_budget_proved':True,
    'all_continuing_prefix_resources_at_original_budget_proved':True,
    'whole_real_worker_and_joint_finite_completion_proved':False},indent=2)+'\\n')
'''
(run / 'check.py').write_text(driver)
pins.append(run / 'check.py')
(run / 'source-pins.json').write_text(json.dumps({str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest()
    for p in pins}, indent=2) + '\n')
print(json.dumps({'run':str(run),'objects':str(objects),'jobs':len(jobs),
    'all_outcome_reports':jobs[1][2],'continuing_reports':jobs[2][2]}))
