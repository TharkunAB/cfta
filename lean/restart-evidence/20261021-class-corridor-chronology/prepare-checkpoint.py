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
assert {'chronology', 'independent-review'} <= paths <= {'chronology', 'independent-review', 'positive-plan'}
selection = json.loads((HERE / 'chronology/chronology-selection.json').read_text())
name = 'lean/MicroCFTA/SourceCurrentClassCorridorChronology.lean'
digest = hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
assert digest == selection['source_sha256'] == 'aaa17d7fb9280fd7f027ee18b17b363824c2c9d0990433a7b7a47d16af99e080'
write('selected-sources.json', {name: {'sha256': digest}})
write('frozen-modules.json', {Path(name).stem: digest})
write('selected-checks.json', {'strict': 'chronology-strict-1', 'audit': 'audit-1', 'public': 'chronology/' + selection['selected_public']})
(HERE / 'root-support').mkdir(exist_ok=True)
previous = HERE / 'previous-publication-support'
previous.mkdir()
for pattern in ['mcfta-class-endpoint-corridors-publication.json', 'mcfta-class-endpoint-corridors-final-publication*',
                'mcfta-class-endpoint-corridors-final-push.log', 'mcfta-class-endpoint-corridors-final-remote.txt',
                'mcfta-class-endpoint-corridors-board-readback.json', 'mcfta-class-endpoint-corridors-seal-1.*',
                'mcfta-class-endpoint-corridors-support-1.*']:
    found = [path for path in Path('/tmp').glob(pattern) if path.is_file()]
    assert found, pattern
    for source in found:
        shutil.copyfile(source, previous / source.name)
print(json.dumps({'status': 'PASS', 'components': len(components), 'new_modules': 1}))

