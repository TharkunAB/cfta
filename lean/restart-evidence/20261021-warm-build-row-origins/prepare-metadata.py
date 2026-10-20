import hashlib
import json
import shutil
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def write(name, value):
    (HERE / name).write_text(json.dumps(value, indent=2) + '\n')


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


sources = {}
for name, strict in [
    ('SourceCurrentNativeOriginalPublicationTrace', 'root-warm-trace-strict-1'),
    ('SourceCurrentWarmBuildRowOrigins', 'root-warm-rows-strict-3'),
]:
    path = 'lean/MicroCFTA/' + name + '.lean'
    sources[path] = {'sha256': sha(ROOT / path), 'strict': strict}
write('selected-sources.json', sources)
write('frozen-modules.json', {name.split('/')[-1][:-5]: entry['sha256'] for name, entry in sources.items()})
fixture_source = 'warm-fixture/warm-row-kernels.lean'
write('selected-fixture.json', {'source': fixture_source, 'strict': 'root-warm-fixture-strict-1',
    'sha256': sha(HERE / fixture_source), 'families': 0, 'reused_source_families': 1,
    'consumer_pairs': 1, 'actual_native_prefix': False, 'actual_unfold': False})
write('selected-public-heads.json', [
    'MicroCFTA.SourceCurrentNativeOriginalPublicationTrace.build_trace_warm_writers',
    'MicroCFTA.SourceCurrentNativeOriginalPublicationTrace.build_trace_warm_target',
    'MicroCFTA.SourceCurrentWarmBuildRowOrigins.RowOrigin',
    'MicroCFTA.SourceCurrentWarmBuildRowOrigins.build_row_origins'])
write('component-status.json', [
    {'path': 'warm-trace', 'current': True, 'live_verified': True},
    {'path': 'warm-rows', 'current': False, 'historical_source': 'f0948519',
     'final_portable_verified': True, 'live_at_archive_time': True},
    {'path': 'warm-prefix', 'current': True, 'live_verified': True},
    {'path': 'warm-fixture', 'current': True, 'live_verified': True}])
support = HERE / 'root-support'
support.mkdir(exist_ok=True)
for stem in ['mcfta-warm-row-start-1', 'mcfta-warm-trace-archive-1',
             'mcfta-warm-rows-archive-1', 'mcfta-warm-prefix-archive-1',
             'mcfta-warm-proof-push-1', 'mcfta-warm-prefix-push-1',
             'mcfta-warm-preservation-1', 'mcfta-warm-fixture-archive-1']:
    for suffix in ['json', 'log', 'limits.json', 'peaks.txt', 'source.py', 'usage.json']:
        source = Path('/tmp') / (stem + '.' + suffix)
        assert source.exists(), source
        shutil.copyfile(source, support / source.name)
print(json.dumps({'status': 'PASS', 'selected_source_files': len(sources),
                  'new_public_theorems': 3, 'new_public_definitions': 1, 'consumer_pairs': 1}))
