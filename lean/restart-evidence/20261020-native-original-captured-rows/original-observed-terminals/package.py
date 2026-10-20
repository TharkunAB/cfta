import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = Path('/home/tritlo/Code/mcfta')


def pin(base, path):
    data = (base / path).read_bytes()
    return {'path': path, 'sha256': hashlib.sha256(data).hexdigest(), 'bytes': len(data)}


names = ['SourceCurrentNativeCapturedMuUnfoldRows', 'SourceCurrentNativeOriginalRowTerminals',
         'SourceCurrentNativeCapturedMuStoredRows', 'SourceCurrentSourceRowTerminalSuffix',
         'SourceCurrentSourceCaptureOriginalSlots', 'SourceCurrentBuildStructuralRowOrigins',
         'InternedFreshOrdinarySourceHistory', 'SourceCurrentNativeMuPublication',
         'SourceCurrentStoredLiteralRowLineage', 'SourceCurrentStoredSubstitutionCalls']
paths = ['lean/MicroCFTA/' + name + '.lean' for name in names]
(HERE / 'observed-terminal-source-pins.json').write_text(json.dumps({'files': [pin(ROOT, path) for path in paths]}, indent=2) + '\n')
(HERE / 'observed-terminal-peaks-final.txt').write_bytes((HERE / 'observed-terminal-peaks.txt').read_bytes())
files = ['SourceCurrentNativeOriginalObservedTerminals.lean', 'observed-terminal-run-check.py',
         'observed-terminal-capped-worker.py', 'observed-terminal-public.lean',
         'observed-terminal-peaks-final.txt', 'observed-terminal-selection.json',
         'observed-terminal-review.md', 'observed-terminal-source-pins.json',
         'observed-terminal-verify.py', 'package.py']
for stem in ['observed-terminal-direct-1', 'observed-terminal-direct-2', 'observed-terminal-public-1']:
    files += [stem + end for end in ['.json', '.source.lean', '.log', '.limits.json', '.usage.json']]
(HERE / 'observed-terminal-manifest.json').write_text(json.dumps({
    'schema': 1, 'files': [pin(HERE, path) for path in files],
    'sources': [pin(ROOT, path) for path in paths]}, indent=2) + '\n')
