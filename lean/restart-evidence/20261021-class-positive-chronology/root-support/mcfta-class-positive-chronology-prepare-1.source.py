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
assert {'chronology', 'independent-review', 'required-plan'} == paths
config = [
    ('chronology', 'positive-chronology', 'SourceCurrentClassPositiveChronology',
     '38f14f1c54e09147d4a19f79b5f938f71ae28eaad3bf102f5b1d37b3f28b1d7a'),
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
for pattern in ['mcfta-class-positive-ancestry-publication.json', 'mcfta-class-positive-ancestry-final-publication*',
                'mcfta-class-positive-ancestry-final-push.log', 'mcfta-class-positive-ancestry-final-remote.txt',
                'mcfta-class-positive-ancestry-board-readback.json', 'mcfta-class-positive-ancestry-seal-1.*',
                'mcfta-class-positive-ancestry-support-1.*']:
    found = [path for path in Path('/tmp').glob(pattern) if path.is_file()]
    assert found, pattern
    for source in found:
        shutil.copyfile(source, previous / source.name)
print(json.dumps({'status': 'PASS', 'components': len(components), 'new_modules': len(config)}))
