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
assert {'rank-envelope', 'independent-review', 'rank-envelope-plan', 'rank-envelope-plan-review'} == paths
config = [
    ('rank-envelope', 'outer-rank-envelope', 'SourceCurrentOuterRankEnvelope',
     'b8401732ae63be4d2036ccd4af7997b787ced8787789a1fb9d2e354047fde5ba'),
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
for pattern in ['mcfta-outer-done-or-exhausted-publication.json', 'mcfta-outer-done-or-exhausted-final-publication*',
                'mcfta-outer-done-or-exhausted-final-push.log', 'mcfta-outer-done-or-exhausted-final-remote.txt',
                'mcfta-outer-done-or-exhausted-board-readback.json', 'mcfta-outer-done-or-exhausted-seal-1.*',
                'mcfta-outer-done-or-exhausted-support-1.*']:
    found = [path for path in Path('/tmp').glob(pattern) if path.is_file()]
    assert found, pattern
    for source in found:
        shutil.copyfile(source, previous / source.name)
print(json.dumps({'status': 'PASS', 'components': len(components), 'new_modules': len(config)}))
