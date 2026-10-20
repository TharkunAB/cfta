import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = Path('/home/tritlo/Code/mcfta')


def pin(base, path):
    data = (base / path).read_bytes()
    return {'path': path, 'sha256': hashlib.sha256(data).hexdigest(), 'bytes': len(data)}


paths = ['lean/MicroCFTA/' + name + '.lean' for name in [
    'SourceCurrentNativeReferenceOrigins', 'SourceCurrentNativeActiveQueryForwarding',
    'SourceCurrentNativeWriterReadyRetention', 'SourceCurrentAllocatedNativeSemanticTraceReadback',
    'SourceCurrentAllocatedNativePhysicalTraceCompletion', 'SourceCurrentAllocatedNativeCodeFields',
    'SourceRecursiveIntersectionCompile', 'InternedStoredSubstitution',
    'SourceCurrentNativeActiveMuBodyOrigins', 'SourceCurrentNativeActiveRowOrigins',
    'SourceCurrentNativeOpenRowOrigins', 'SourceCurrentNativeCapturedMuOrigins']]
(HERE / 'active-reference-source-pins.json').write_text(json.dumps({'files': [pin(ROOT, p) for p in paths]}, indent=2) + '\n')
files = ['SourceCurrentNativeActiveReferenceOrigins.lean', 'active-reference-run-check.py',
         'active-reference-capped-worker.py', 'active-reference-public.lean',
         'active-reference-peaks-final.txt', 'active-reference-selection.json',
         'active-reference-review.md', 'active-reference-semantic-map.md',
         'active-reference-source-pins.json', 'active-reference-verify.py', 'package.py']
for stem in ['active-reference-direct-1', 'active-reference-public-1']:
    files += [stem + ending for ending in ['.json', '.limits.json', '.usage.json', '.source.lean', '.log']]
(HERE / 'active-reference-manifest.json').write_text(json.dumps({
    'schema': 1, 'files': [pin(HERE, p) for p in files], 'sources': [pin(ROOT, p) for p in paths]}, indent=2) + '\n')
