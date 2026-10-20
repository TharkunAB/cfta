import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = Path('/home/tritlo/Code/mcfta')


def pin(base, path):
    data = (base / path).read_bytes()
    return {'path': path, 'sha256': hashlib.sha256(data).hexdigest(), 'bytes': len(data)}


names = ['SourceCurrentSourceRowTerminalSuffix', 'SourceCurrentSourceCaptureOriginalSlots',
         'InternedFreshOrdinarySourceHistory', 'InternedFreshOrdinaryActiveOrigins',
         'SourceCurrentBuildStructuralRowOrigins', 'SourceCurrentRootedRowChildOrigins',
         'SourceCurrentConstrainedCapSourceHistory', 'SourceCurrentStoredLiteralRowLineage',
         'InternedFreshOrdinaryFacts', 'InternedFreshOrdinaryConstruction']
paths = ['lean/MicroCFTA/' + name + '.lean' for name in names]
(HERE / 'original-row-terminal-source-pins.json').write_text(json.dumps({'files': [pin(ROOT, path) for path in paths]}, indent=2) + '\n')
(HERE / 'original-row-terminal-peaks-final.txt').write_bytes((HERE / 'original-row-terminal-peaks.txt').read_bytes())
files = ['SourceCurrentNativeOriginalRowTerminals.lean', 'original-row-terminal-run-check.py',
         'original-row-terminal-capped-worker.py', 'original-row-terminal-public.lean',
         'original-row-terminal-peaks-final.txt', 'original-row-terminal-selection.json',
         'original-row-terminal-review.md', 'original-row-terminal-source-pins.json',
         'original-row-terminal-verify.py', 'package.py']
for stem in ['original-row-terminal-direct-1', 'original-row-terminal-direct-2', 'original-row-terminal-public-1']:
    files += [stem + end for end in ['.json', '.source.lean', '.log', '.limits.json', '.usage.json']]
(HERE / 'original-row-terminal-manifest.json').write_text(json.dumps({
    'schema': 1, 'files': [pin(HERE, path) for path in files],
    'sources': [pin(ROOT, path) for path in paths]}, indent=2) + '\n')
