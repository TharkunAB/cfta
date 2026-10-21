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
assert {'forest-cap', 'independent-review'} <= paths <= {'forest-cap', 'independent-review', 'target-plan'}
selection = json.loads((HERE / 'forest-cap/forest-cap-selection.json').read_text())
name = 'lean/MicroCFTA/SourceCurrentRequiredForestProjectionCap.lean'
digest = hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
assert digest == selection['source_sha256'] == '7569b823aa8b9d5a1935664fceb2630268fdd2641169d2f2e7bd87f9daee1e95'
write('selected-sources.json', {name: {'sha256': digest}})
write('frozen-modules.json', {Path(name).stem: digest})
write('selected-checks.json', {'strict': 'forest-strict-1', 'audit': 'audit-1', 'public': 'forest-cap/' + selection['selected_public']})
(HERE / 'root-support').mkdir(exist_ok=True)
previous = HERE / 'previous-publication-support'
previous.mkdir()
for pattern in ['mcfta-original-gate-projection-cap-publication.json', 'mcfta-original-gate-projection-cap-final-publication*',
                'mcfta-original-gate-projection-cap-final-push.log', 'mcfta-original-gate-projection-cap-final-remote.txt',
                'mcfta-original-gate-projection-cap-board-readback.json', 'mcfta-original-gate-projection-cap-seal-1.*',
                'mcfta-original-gate-projection-cap-support-1.*']:
    found = [path for path in Path('/tmp').glob(pattern) if path.is_file()]
    assert found, pattern
    for source in found:
        shutil.copyfile(source, previous / source.name)
print(json.dumps({'status': 'PASS', 'components': len(components), 'new_modules': 1}))

