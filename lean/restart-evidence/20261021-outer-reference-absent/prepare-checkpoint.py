import hashlib
import json
import shutil
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]

def write(name, value):
    (HERE / name).write_text(json.dumps(value, indent=2) + '\n')

components = json.loads((HERE / 'components.json').read_text())
paths = {item['path'] for item in components}
assert {'reference-absent', 'independent-review', 'next-fault-plan', 'next-fault-plan-review'} == paths
config = [
    ('reference-absent', 'outer-reference-absent', 'SourceCurrentOuterReferenceAbsent',
     'e478e51b56ec1ecf2a613bf7f115688b745c1e01a9b9718c19b643f8f6045263'),
]
sources, frozen, checks = {}, {}, {}
for tag, prefix, module, expected in config:
    selection = json.loads((HERE / tag / (prefix + '-selection.json')).read_text())
    name = 'lean/MicroCFTA/' + module + '.lean'
    digest = hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
    assert digest == selection['source_sha256'] == expected
    sources[name] = {'sha256': digest}
    frozen[module] = digest
    checks[tag] = {'strict': tag + '-strict-1', 'public': tag + '/' + selection['selected_public']}
write('selected-sources.json', sources)
write('frozen-modules.json', frozen)
write('selected-checks.json', {**checks, 'audit': 'audit-1'})
previous = HERE / 'previous-publication-support'
previous.mkdir()
for pattern in ['mcfta-outer-closed-inputs-publication.json', 'mcfta-outer-closed-inputs-final-publication*',
                'mcfta-outer-closed-inputs-final-push.log', 'mcfta-outer-closed-inputs-final-remote.txt',
                'mcfta-outer-closed-inputs-board-readback.json', 'mcfta-outer-closed-inputs-seal-1.*',
                'mcfta-outer-closed-inputs-support-1.*']:
    found = [path for path in Path('/tmp').glob(pattern) if path.is_file()]
    assert found, pattern
    for source in found:
        shutil.copyfile(source, previous / source.name)
print(json.dumps({'status': 'PASS', 'components': len(components), 'new_modules': len(config)}))
