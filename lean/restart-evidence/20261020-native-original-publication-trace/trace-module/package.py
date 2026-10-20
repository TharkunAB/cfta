import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = Path('/home/tritlo/Code/mcfta')


def pin(base, path):
    data = (base / path).read_bytes()
    return {'path': path, 'sha256': hashlib.sha256(data).hexdigest(), 'bytes': len(data)}


names = ['SourceCurrentCompletedBuildRootedWriters', 'SourceCurrentNativeMuIssuedHistory',
         'SourceCurrentNativeMuIssuedWriters', 'SourceCurrentNativeMuGrowthHistory',
         'SourceCurrentNativeMuPublication', 'SourceCurrentNativeMuPublicationCallbacks',
         'SourceCurrentConstrainedCapSourceHistory', 'InternedFreshOrdinarySourceHistory',
         'InternedFreshOrdinaryActiveOrigins', 'InternedFreshOrdinaryFacts',
         'InternedFreshOrdinaryConstruction', 'InternedShallowHeap']
paths = ['lean/MicroCFTA/' + name + '.lean' for name in names]
(HERE / 'publication-trace-source-pins.json').write_text(json.dumps({'files': [pin(ROOT, path) for path in paths]}, indent=2) + '\n')
(HERE / 'publication-trace-peaks-final.txt').write_bytes((HERE / 'publication-trace-peaks.txt').read_bytes())
files = ['SourceCurrentNativeOriginalPublicationTrace.lean', 'publication-trace-run-check.py',
         'publication-trace-capped-worker.py', 'publication-trace-public.lean',
         'publication-trace-peaks-final.txt', 'publication-trace-selection.json',
         'publication-trace-review.md', 'publication-trace-source-pins.json',
         'publication-trace-verify.py', 'package.py', 'header.lean.txt',
         'public-producer.lean.txt', 'order-helpers-snippet.lean.txt']
for stem in ['publication-trace-direct-1', 'publication-trace-direct-2', 'publication-trace-direct-3',
             'publication-trace-public-1']:
    files += [stem + end for end in ['.json', '.source.lean', '.log', '.limits.json', '.usage.json']]
(HERE / 'publication-trace-manifest.json').write_text(json.dumps({
    'schema': 1, 'files': [pin(HERE, path) for path in files],
    'sources': [pin(ROOT, path) for path in paths]}, indent=2) + '\n')
