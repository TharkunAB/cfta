import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = Path('/home/tritlo/Code/mcfta')


def pin(base, path):
    data = (base / path).read_bytes()
    return {'path': path, 'sha256': hashlib.sha256(data).hexdigest(), 'bytes': len(data)}


paths = ['lean/MicroCFTA/' + name + '.lean' for name in [
    'SourceCurrentNativeActiveMuBodyOrigins', 'SourceCurrentNativeMuWriterSourceRows',
    'SourceCurrentNativeQueryMuRowOrigins', 'SourceCurrentNativeConstructReaderReadback',
    'SourceCurrentNativeConstructSourceRows', 'SourceCurrentNativePrefixWriterMaps',
    'SourceCurrentNativePublicationTrace', 'SourceCurrentNativeMuPublication',
    'SourceCurrentNativeNormalizedComparisonExecution', 'SourceCurrentNativeCallbackRowOrigins',
    'SourceCurrentNativeOrdinaryMuFinish', 'SourceCurrentNativeActiveQueryForwarding',
    'SourceCurrentNativeWriterReadyRetention', 'SourceCurrentNativeMuBodyOrigins']]
(HERE / 'active-mu-row-source-pins.json').write_text(json.dumps({'files': [pin(ROOT, p) for p in paths]}, indent=2) + '\n')
files = ['SourceCurrentNativeActiveMuRowReadback.lean', 'active-mu-row-run-check.py',
         'active-mu-row-capped-worker.py', 'active-mu-row-public.lean',
         'active-mu-row-peaks-final.txt', 'active-mu-row-selection.json',
         'active-mu-row-review.md', 'active-mu-row-source-pins.json',
         'active-mu-row-verify.py', 'package.py']
for stem in ['active-mu-row-direct-1', 'active-mu-row-direct-2', 'active-mu-row-public-1']:
    files += [stem + ending for ending in ['.json', '.limits.json', '.usage.json', '.source.lean', '.log']]
(HERE / 'active-mu-row-manifest.json').write_text(json.dumps({
    'schema': 1, 'files': [pin(HERE, p) for p in files], 'sources': [pin(ROOT, p) for p in paths]}, indent=2) + '\n')
