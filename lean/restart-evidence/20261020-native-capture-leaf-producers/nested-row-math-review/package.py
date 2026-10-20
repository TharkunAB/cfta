import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = Path('/home/tritlo/Code/mcfta')
FIXTURE = 'lean/restart-evidence/20261020-native-capture-leaf-producers/nested-mu-row-capture-fixture/'


def pin(base, path):
    data = (base / path).read_bytes()
    return {'path': path, 'sha256': hashlib.sha256(data).hexdigest(), 'bytes': len(data)}


paths = [FIXTURE + name for name in ['captured-row-kernels.lean', 'captured-row-kernels-selection.json',
         'captured-row-kernels-manifest.json', 'captured-row-kernels-verify.py']]
for stem in ['captured-row-kernels-direct-1', 'captured-row-kernels-public-1']:
    paths += [FIXTURE + stem + suffix for suffix in ['.json', '.source.lean', '.log', '.limits.json', '.usage.json']]
names = ['SourceCurrentNativeCapturedMuRowProduction', 'SourceCurrentNativeOptionalRowProduction',
         'SourceCurrentNativeActiveRowProduction', 'SourceCurrentNativeMuOptionalGeneration',
         'SourceCurrentAllocatedRecursivePrefixAdmission', 'SourceCurrentAllocatedRecursivePrefixCode',
         'SourceCurrentAllocatedRecursivePrefixState', 'SourceCurrentAllocatedNativePhysicalTraceCompletion',
         'SourceCurrentNativeOptionalTerminalOrigin', 'SourceCurrentNativePrefixWriterMaps']
paths += ['lean/MicroCFTA/' + name + '.lean' for name in names]
(HERE / 'source-pins.json').write_text(json.dumps({'files': [pin(ROOT, path) for path in paths]}, indent=2) + '\n')
(HERE / 'selection.json').write_text(json.dumps({
    'finalized': True, 'kind': 'source-only-review', 'owned_jobs': 0, 'owned_pairs': 0,
    'reused_constructed_pairs': 1, 'count_prior_concrete_family_separately': False,
    'source_sha256': '8807b07779bc396921b3d13e235be8c97d3705bc2f9a197172c428b57735e29c'}, indent=2) + '\n')
files = ['reviewed-fixture.lean', 'review.md', 'source-pins.json', 'selection.json', 'verify.py', 'package.py']
(HERE / 'manifest.json').write_text(json.dumps({
    'schema': 1, 'files': [pin(HERE, path) for path in files],
    'sources': [pin(ROOT, path) for path in paths]}, indent=2) + '\n')
