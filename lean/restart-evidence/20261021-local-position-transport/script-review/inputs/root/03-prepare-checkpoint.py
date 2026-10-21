import hashlib
import json
import shutil
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
def write(name, value):
    (HERE / name).write_text(json.dumps(value, indent=2) + '\n')
components = json.loads((HERE / 'components.json').read_text())
assert {'maybe-mu', 'maybe-mu-review', 'target', 'target-review'} <= {item['path'] for item in components}
names = ['SourceCurrentNativeMaybeMuPositivePositions', 'SourceCurrentTargetOperandPositivePosition']
sources = {'lean/MicroCFTA/' + name + '.lean': {'sha256': hashlib.sha256((ROOT / 'lean/MicroCFTA' / (name + '.lean')).read_bytes()).hexdigest()} for name in names}
write('selected-sources.json', sources)
write('frozen-modules.json', {Path(name).stem: item['sha256'] for name, item in sources.items()})
write('selected-checks.json', {'strict': ['maybe-mu-strict-1', 'target-strict-1'], 'audit': 'audit-1',
                             'public': ['maybe-mu/maybe-mu-position-public-1', 'target/target-position-public-1']})
support = HERE / 'root-support'
support.mkdir()
for stem in ['baseline-1', 'plans-1', 'maybe-archive-1', 'maybe-review-archive-1',
             'target-archive-1', 'target-review-archive-1', 'maybe-proof-push-1', 'audit-import-fix-1', 'target-proof-push-1']:
    for suffix in ['json', 'log', 'limits.json', 'peaks.txt', 'source.py', 'usage.json']:
        source = Path('/tmp') / ('mcfta-local-position-transport-' + stem + '.' + suffix)
        assert source.is_file(), source
        shutil.copyfile(source, support / source.name)
previous = HERE / 'previous-publication-support'
previous.mkdir()
for pattern in ['mcfta-stored-mu-position-publication.json', 'mcfta-stored-mu-position-final-publication*',
                'mcfta-stored-mu-position-final-push.log', 'mcfta-stored-mu-position-final-remote.txt',
                'mcfta-stored-mu-position-board-readback.json', 'mcfta-stored-mu-position-seal-1.*',
                'mcfta-stored-mu-position-support-1.*']:
    found = [path for path in Path('/tmp').glob(pattern) if path.is_file()]
    assert found, pattern
    for source in found:
        shutil.copyfile(source, previous / source.name)
print(json.dumps({'status': 'PASS', 'components': len(components), 'new_modules': len(names)}))
