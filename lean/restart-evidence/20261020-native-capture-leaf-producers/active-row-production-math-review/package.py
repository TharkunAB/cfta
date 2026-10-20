import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = Path('/home/tritlo/Code/mcfta')


def pin(base, path):
    data = (base / path).read_bytes()
    return {'path': path, 'sha256': hashlib.sha256(data).hexdigest(), 'bytes': len(data)}


names = ['SourceCurrentNativeActivePairedRows', 'SourceCurrentNativeActiveUnionRowOrigins',
         'SourceCurrentNativeActiveReferenceOrigins', 'SourceCurrentNativeActiveMuBodyOrigins',
         'SourceCurrentNativeActiveQueryForwarding', 'SourceCurrentNativeMuBodyOrigins',
         'SourceCurrentNativeWriterReadyRetention', 'SourceCurrentNativeEdgeWriterRetention',
         'SourceCurrentNativeForwardLineage', 'SourceCurrentNativeQueryRowOrigins',
         'SourceRecursiveIntersectionCompile', 'SourceCurrentNativePrefixWriterMaps']
paths = ['lean/MicroCFTA/' + name + '.lean' for name in names]
stem = 'lean/restart-evidence/20261020-native-capture-leaf-producers/root-active-production-strict-1'
paths += [stem + end for end in ['.json', '.source.lean', '.log', '.limits.json', '.usage.json']]
(HERE / 'source-pins.json').write_text(json.dumps({'files': [pin(ROOT, path) for path in paths]}, indent=2) + '\n')
(HERE / 'selection.json').write_text(json.dumps({
    'finalized': True, 'kind': 'source-only-review',
    'source_sha256': '2bd2013dc8f3f30e81eb0feae618b5e0f3f871e94e7b7f6833329d95fbb2a76f',
    'owned_jobs': 0, 'owned_pairs': 0, 'reviewed_source_heads': 7,
    'reused_strict': stem, 'reused_full_pairs': 0}, indent=2) + '\n')
files = ['reviewed-production.lean', 'review.md', 'source-pins.json', 'selection.json', 'verify.py', 'package.py']
(HERE / 'manifest.json').write_text(json.dumps({
    'schema': 1, 'files': [pin(HERE, path) for path in files],
    'sources': [pin(ROOT, path) for path in paths]}, indent=2) + '\n')
