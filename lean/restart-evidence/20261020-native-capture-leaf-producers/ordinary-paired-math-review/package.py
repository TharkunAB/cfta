import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = Path('/home/tritlo/Code/mcfta')


def pin(base, path):
    data = (base / path).read_bytes()
    return {'path': path, 'sha256': hashlib.sha256(data).hexdigest(), 'bytes': len(data)}


names = ['SourceCurrentNativeOrdinaryLeafOrigins', 'SourceCurrentNativeActivePairedRows',
         'SourceCurrentNativeActiveRowOrigins', 'SourceCurrentIndexedFirstOrdinaryCut',
         'InternedStoredSubstitution', 'SourceCurrentNativeRowOrigins',
         'SourceCurrentNativePrefixWriterMaps', 'SourceCurrentNativeWriterReadyRetention',
         'SourceCurrentNativeEdgeWriterRetention', 'SourceCurrentNativeWriterChildRetention',
         'SourceCurrentNativeReaderRowLineage', 'SourceCurrentAllocatedNativeSemanticTraceReadback']
paths = ['lean/MicroCFTA/' + name + '.lean' for name in names]
stems = ['lean/restart-evidence/20261020-native-capture-leaf-producers/root-' + name + '-strict-1'
         for name in ['ordinary-leaf', 'paired-rows']]
for stem in stems:
    paths += [stem + end for end in ['.json', '.source.lean', '.log', '.limits.json', '.usage.json']]
(HERE / 'source-pins.json').write_text(json.dumps({'files': [pin(ROOT, path) for path in paths]}, indent=2) + '\n')
(HERE / 'selection.json').write_text(json.dumps({
    'finalized': True, 'kind': 'source-only-review', 'owned_jobs': 0, 'owned_pairs': 0,
    'reviewed_source_heads': 4, 'reused_strict': stems, 'reused_full_pairs': 0,
    'fixture_included': False}, indent=2) + '\n')
files = ['reviewed-ordinary-leaf.lean', 'reviewed-paired-rows.lean', 'review.md',
         'source-pins.json', 'selection.json', 'verify.py', 'package.py']
(HERE / 'manifest.json').write_text(json.dumps({
    'schema': 1, 'files': [pin(HERE, path) for path in files],
    'sources': [pin(ROOT, path) for path in paths]}, indent=2) + '\n')
