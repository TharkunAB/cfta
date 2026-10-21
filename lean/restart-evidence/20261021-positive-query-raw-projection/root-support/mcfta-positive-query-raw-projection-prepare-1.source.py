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
assert {'query', 'projection', 'entry', 'independent-review', 'query-review', 'raw-plan', 'entry-plan'} <= paths
config = [
    ('query', 'current-position', 'SourceCurrentNativeCurrentPositivePositions',
     '01a135ec67ebb6937106a4958c7efa418d02af1eb9c061a7c07bf6727fc5b577'),
    ('projection', 'raw-positive', 'SourceCurrentRawCorridorPositiveProjection',
     'c87599728b99a77e5c0a64d1836986f05142dcabe99ffafff75454ce2d4179d1'),
    ('entry', 'entry', 'SourceCurrentRequiredCorridorChronology',
     '71f589094a700a859b05a41adb83845177d27ace0dfad118542acf9d9d3c9592'),
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
for pattern in ['mcfta-class-corridor-chronology-publication.json', 'mcfta-class-corridor-chronology-final-publication*',
                'mcfta-class-corridor-chronology-final-push.log', 'mcfta-class-corridor-chronology-final-remote.txt',
                'mcfta-class-corridor-chronology-board-readback.json', 'mcfta-class-corridor-chronology-seal-1.*',
                'mcfta-class-corridor-chronology-support-1.*']:
    found = [path for path in Path('/tmp').glob(pattern) if path.is_file()]
    assert found, pattern
    for source in found:
        shutil.copyfile(source, previous / source.name)
print(json.dumps({'status': 'PASS', 'components': len(components), 'new_modules': len(config)}))
