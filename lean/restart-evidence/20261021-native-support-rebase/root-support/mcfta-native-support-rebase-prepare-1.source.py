import hashlib
import json
import shutil
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]

def write(name, value):
    (HERE / name).write_text(json.dumps(value, indent=2) + '\n')

components = json.loads((HERE / 'components.json').read_text())
assert {item['path'] for item in components} == {'rebase', 'independent-review', 'class-observation-plan'}
name = 'lean/MicroCFTA/SourceCurrentNativePositiveSupportRebase.lean'
digest = hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
assert digest == 'bcd4ae7e4690f4c5ceb661328484d7b84e42a3b1b493bc2a3cfac57333e25ee6'
write('selected-sources.json', {name: {'sha256': digest}})
write('frozen-modules.json', {Path(name).stem: digest})
write('selected-checks.json', {'strict': 'rebase-strict-1', 'audit': 'audit-1', 'public': 'rebase/rebase-public-1'})
(HERE / 'root-support').mkdir(exist_ok=True)
previous = HERE / 'previous-publication-support'
previous.mkdir()
for pattern in ['mcfta-native-request-position-publication.json', 'mcfta-native-request-position-final-publication*',
                'mcfta-native-request-position-final-push.log', 'mcfta-native-request-position-final-remote.txt',
                'mcfta-native-request-position-board-readback.json', 'mcfta-native-request-position-seal-1.*',
                'mcfta-native-request-position-support-1.*']:
    found = [path for path in Path('/tmp').glob(pattern) if path.is_file()]
    assert found, pattern
    for source in found:
        shutil.copyfile(source, previous / source.name)
print(json.dumps({'status': 'PASS', 'components': len(components), 'new_modules': 1}))

