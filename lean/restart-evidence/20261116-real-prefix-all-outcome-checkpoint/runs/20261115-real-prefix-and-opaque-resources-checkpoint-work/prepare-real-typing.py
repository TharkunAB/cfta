from pathlib import Path
import hashlib
import json
import shlex
import tempfile

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
raw = base / '20261116-current-real-prefix-all-outcome-typing-repair'
prior = base / '20261115-current-real-prefix-all-outcome-resources-draft'
for name in ['PUBLIC-HEADER.lean.txt', 'ZERO-HEADER.lean.txt', 'NONCONTINUING-HEADER.lean.txt',
             'PROBES.lean.txt', 'REMAINING-CONTINUING-TARGET-UNPROVED.lean.txt']:
    assert (raw / name).read_bytes() == (prior / name).read_bytes(), name
name = 'SourcePruningEnumerationRealPrefixAllResources.lean'
assert hashlib.sha256((raw / name).read_bytes()).hexdigest() == 'f350538dffec54109541e43449e402c0c9a2482db647236e620efb09e95a6340'
run = base / '20261116-native-real-prefix-all-outcome-typing-check'
run.mkdir()
source = run / 'source/MicroCFTA' / name
source.parent.mkdir(parents=True)
source.write_bytes((raw / name).read_bytes() + b'\n' + (raw / 'PROBES.lean.txt').read_bytes())
objects = Path(tempfile.mkdtemp(prefix='mcfta-real-prefix-proof-'))
(run / 'objects.json').write_text(json.dumps({'path': str(objects)}, indent=2) + '\n')
modules = [line.split()[1] for line in (raw / name).read_text().splitlines() if line.startswith('import ')]
jobs = [('public-dependencies', 'exec lake build ' + ' '.join(map(shlex.quote, modules)), 0),
    ('real-prefix-all-outcome-typing', 'exec lake env lean -j1 -DwarningAsError=true -R '
        + shlex.quote(str(source.parent.parent)) + ' -o ' + shlex.quote(str(objects / 'RealPrefix.olean'))
        + ' ' + shlex.quote(str(source)), (raw / 'PROBES.lean.txt').read_text().count('#print axioms '))]
template = (base / '20261115-native-open-binder-helper-dependencies/check.py').read_text()
driver = template[:template.index('run("public-dependency"')]
driver += 'jobs = ' + repr(jobs) + '\nfor name, command, count in jobs:\n    run(name, command, count)\n'
driver += '''(runtime/'checked.json').write_text(json.dumps({'checks':checks,'source_pins_unchanged':True,
    'all_real_prefix_tag_resources_at_original_budget_proved':True,
    'continuing_prefix_resources_all_cases_proved':False,
    'whole_real_worker_and_joint_finite_completion_proved':False},indent=2)+'\\n')
'''
(run / 'check.py').write_text(driver)
pins = list((root / 'lean/MicroCFTA').glob('*.lean'))
pins += [root / p for p in ['shell.nix', 'lean/lean-toolchain', 'lean/lakefile.toml', 'lean/lake-manifest.json']]
pins += [Path(__file__), raw / name, raw / 'PROBES.lean.txt', source, run / 'check.py']
(run / 'source-pins.json').write_text(json.dumps({str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest()
    for p in pins}, indent=2) + '\n')
print(json.dumps({'run':str(run),'objects':str(objects),'jobs':len(jobs),'reports':jobs[1][2]}))
