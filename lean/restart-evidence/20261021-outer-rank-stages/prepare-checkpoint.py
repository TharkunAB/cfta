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
assert {'rank-stages', 'independent-review', 'stage-plan', 'stage-plan-review'} == paths
config = [
    ('rank-stages', 'outer-rank-stages', 'SourceCurrentOuterRankEnvelopeStages',
     '6183fb57a67754f0b616d10e2cbe40979d4958916d6101908d4e76ce5ee0b406'),
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
for pattern in ['mcfta-outer-rank-envelope-publication.json', 'mcfta-outer-rank-envelope-final-publication*',
                'mcfta-outer-rank-envelope-final-push.log', 'mcfta-outer-rank-envelope-final-remote.txt',
                'mcfta-outer-rank-envelope-board-readback.json', 'mcfta-outer-rank-envelope-seal-1.*',
                'mcfta-outer-rank-envelope-support-1.*']:
    found = [path for path in Path('/tmp').glob(pattern) if path.is_file()]
    assert found, pattern
    for source in found:
        shutil.copyfile(source, previous / source.name)
print(json.dumps({'status': 'PASS', 'components': len(components), 'new_modules': len(config)}))
