import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = Path('/home/tritlo/Code/mcfta')


def pin(base, path):
    data = (base / path).read_bytes()
    return {'path': path, 'sha256': hashlib.sha256(data).hexdigest(), 'bytes': len(data)}


names = ['SourceCurrentNativeOriginalObservedResume', 'SourceCurrentNativeOriginalBinderResume',
         'SourceCurrentSourceRowTerminalSuffix', 'SourceCurrentNativeOriginalRowTerminals',
         'SourceCurrentSourceCaptureOriginalSlots', 'SourceCurrentBuildStructuralRowOrigins',
         'SourceCurrentNativeCapturedMuUnfoldRows', 'SourceCurrentNativeCapturedMuStoredRows',
         'SourceCurrentConstrainedCapSourceHistory', 'SourceCurrentStoredMuRetainedAlignment',
         'InternedFreshOrdinarySourceHistory', 'InternedFreshOrdinaryFacts']
paths = ['lean/MicroCFTA/' + name + '.lean' for name in names]
(HERE / 'union-descent-source-pins.json').write_text(json.dumps({'files': [pin(ROOT, path) for path in paths]}, indent=2) + '\n')
(HERE / 'union-descent-peaks-final.txt').write_bytes((HERE / 'union-descent-peaks.txt').read_bytes())
files = ['SourceCurrentNativeOriginalUnionDescent.lean', 'union-descent-run-check.py',
         'union-descent-capped-worker.py', 'union-descent-public.lean',
         'union-descent-peaks-final.txt', 'union-descent-selection.json',
         'union-descent-review.md', 'union-descent-source-pins.json',
         'union-descent-verify.py', 'package.py', 'generate.py']
for stem in ['union-descent-direct-1', 'union-descent-public-1']:
    files += [stem + end for end in ['.json', '.source.lean', '.log', '.limits.json', '.usage.json']]
(HERE / 'union-descent-manifest.json').write_text(json.dumps({
    'schema': 1, 'files': [pin(HERE, path) for path in files],
    'sources': [pin(ROOT, path) for path in paths]}, indent=2) + '\n')
