import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = Path('/home/tritlo/Code/mcfta')


def pin(base, path):
    data = (base / path).read_bytes()
    return {'path': path, 'sha256': hashlib.sha256(data).hexdigest(), 'bytes': len(data)}


names = ['SourceCurrentNativePublicationRawSuffix', 'SourceCurrentNativeMuGrowthHistory',
         'SourceCurrentNativeRootedMuStoredRows', 'SourceCurrentNativeCapturedMuStoredRows',
         'SourceCurrentCompletedBuildRootedWriters', 'SourceCurrentBuildStructuralRowOrigins',
         'SourceCurrentConstrainedCapSourceHistory', 'SourceCurrentNativeMuPublication',
         'SourceCurrentStoredLiteralRowLineage', 'InternedFreshOrdinaryConstruction']
paths = ['lean/MicroCFTA/' + name + '.lean' for name in names]
(HERE / 'binder-resume-source-pins.json').write_text(json.dumps({'files': [pin(ROOT, path) for path in paths]}, indent=2) + '\n')
(HERE / 'binder-resume-peaks-final.txt').write_bytes((HERE / 'binder-resume-peaks.txt').read_bytes())
files = ['SourceCurrentNativeOriginalBinderResume.lean', 'binder-resume-run-check.py',
         'binder-resume-capped-worker.py', 'binder-resume-public.lean',
         'binder-resume-peaks-final.txt', 'binder-resume-selection.json',
         'binder-resume-review.md', 'binder-resume-source-pins.json',
         'binder-resume-verify.py', 'package.py']
for stem in ['binder-resume-direct-1', 'binder-resume-direct-2', 'binder-resume-direct-3', 'binder-resume-public-1']:
    files += [stem + end for end in ['.json', '.source.lean', '.log', '.limits.json', '.usage.json']]
(HERE / 'binder-resume-manifest.json').write_text(json.dumps({
    'schema': 1, 'files': [pin(HERE, path) for path in files],
    'sources': [pin(ROOT, path) for path in paths]}, indent=2) + '\n')
