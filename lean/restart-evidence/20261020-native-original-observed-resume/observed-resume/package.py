import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = Path('/home/tritlo/Code/mcfta')


def pin(base, path):
    data = (base / path).read_bytes()
    return {'path': path, 'sha256': hashlib.sha256(data).hexdigest(), 'bytes': len(data)}


names = ['SourceCurrentNativeOriginalObservedTerminals', 'SourceCurrentNativeOriginalRowTerminals',
         'SourceCurrentNativeOriginalBinderResume', 'SourceCurrentNativePublicationRawSuffix',
         'SourceCurrentNativeRootedMuStoredRows', 'SourceCurrentNativeCapturedMuStoredRows',
         'SourceCurrentNativeCapturedMuUnfoldRows', 'SourceCurrentBuildStructuralRowOrigins',
         'SourceCurrentStoredMuRetainedAlignment', 'SourceCurrentCompletedBuildRootedWriters']
paths = ['lean/MicroCFTA/' + name + '.lean' for name in names]
(HERE / 'observed-resume-source-pins.json').write_text(json.dumps({'files': [pin(ROOT, path) for path in paths]}, indent=2) + '\n')
(HERE / 'observed-resume-peaks-final.txt').write_bytes((HERE / 'observed-resume-peaks.txt').read_bytes())
files = ['SourceCurrentNativeOriginalObservedResume.lean', 'observed-resume-run-check.py',
         'observed-resume-capped-worker.py', 'observed-resume-public.lean',
         'observed-resume-peaks-final.txt', 'observed-resume-selection.json',
         'observed-resume-review.md', 'observed-resume-source-pins.json',
         'observed-resume-verify.py', 'package.py']
for stem in ['observed-resume-direct-1', 'observed-resume-direct-2', 'observed-resume-public-1']:
    files += [stem + end for end in ['.json', '.source.lean', '.log', '.limits.json', '.usage.json']]
(HERE / 'observed-resume-manifest.json').write_text(json.dumps({
    'schema': 1, 'files': [pin(HERE, path) for path in files],
    'sources': [pin(ROOT, path) for path in paths]}, indent=2) + '\n')
