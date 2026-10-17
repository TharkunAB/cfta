from pathlib import Path
import hashlib
import json
import re

root = Path(__file__).resolve().parents[3]
evidence = root / 'lean/restart-evidence/20261017-recursive-positional'
source = root / 'lean/MicroCFTA/SourceCurrentConstrainedCapPaths.lean'

def entry(path: Path) -> dict[str, str]:
    return {'path': path.relative_to(root).as_posix(), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}

checks = []
for prefix, count in [('paths-public-1', 20), ('paths-kernels-2', 6)]:
    path = evidence / f'{prefix}.log'
    log = path.read_text()
    assert not re.search(r'error|warning|sorryAx|declaration uses', log)
    signatures = re.findall(r'^@([^\s:]+)', log, re.M)
    names = re.findall(r"^'([^']+)' (?:depends on axioms:|does not depend on any axioms)", log, re.M)
    assert len(signatures) == count
    assert signatures == names
    for axioms in re.findall(r'depends on axioms: \[([^\]]*)\]', log, re.S):
        for axiom in axioms.split(','):
            name = re.sub(r'\.\{.*\}', '', axiom.strip())
            assert name in {'propext', 'Classical.choice', 'Quot.sound'}, name
    checks.append({'log': path.relative_to(root).as_posix(), 'exit_code': 0, 'pairs': count, 'warnings': 0, 'errors': 0, 'custom_axioms': 0})
assert (evidence / 'paths-direct-3.log').stat().st_size == 0
assert (evidence / 'paths-direct-3.source.lean').read_bytes() == source.read_bytes()
assert (evidence / 'paths-final.source.lean').read_bytes() == source.read_bytes()
assert (evidence / 'paths-public.lean').read_bytes() == (evidence / 'paths-public-1.source.lean').read_bytes()
assert (evidence / 'paths-kernels.lean').read_bytes() == (evidence / 'paths-kernels-2.source.lean').read_bytes()
validation = {
    'source_sha256': entry(source)['sha256'],
    'lean_version': '4.34.1',
    'strict_direct': {'log': 'paths-direct-3.log', 'exit_code': 0, 'bytes': 0},
    'canonical': {'log': 'cap-read-path-build.log', 'exit_code': 0, 'jobs': 1104, 'module_built': 1102, 'new_warnings': 0, 'historical_dependency_warning': 'InternedFreshOrdinaryClosedCompletion inputs'},
    'imported_probes': checks,
    'preserved_failures': {'paths-direct-1': 'The autoImplicit=false flag differs from repository inference conventions.', 'paths-direct-2': 'A direct import for two hereditary laws was missing.', 'paths-kernels-1': 'A decide goal had free variables. One reference needed an explicit Symbol.'},
    'scope': 'Initial pure signed path masks. Actual zero-tail ProjectRows only. No full getPath, edit closure, or progress theorem.'
}
(evidence / 'paths-validation.json').write_text(json.dumps(validation, indent=2) + '\n')
read_files = [
    'lean/MicroCFTA/SourceCurrentConstrainedCap.lean',
    'lean/MicroCFTA/SourceCurrentConstrainedCapPaths.lean',
    'lean/MicroCFTA/SourceEqualityProjectionGraph.lean',
    'lean/MicroCFTA/SourceEqualityRequiredGraph.lean',
    'lean/MicroCFTA/SourceCurrentAllocatedSharedEditGraph.lean',
    'lean/MicroCFTA/SourceCurrentAllocatedPartialWorker.lean',
    'lean/MicroCFTA/SourceCurrentAllocatedPartialActiveOrder.lean',
    'lean/MicroCFTA/SourceCurrentAllocatedPartialPlainNode.lean',
    'lean/MicroCFTA/SourceCurrentSelectedClassRecords.lean',
    'lean/MicroCFTA/SourceCurrentAllocatedRecordScanWorkerActual.lean',
    'lean/MicroCFTA/SourceCurrentHereditaryUnconstrained.lean',
    'lean/MicroCFTA/SourceEqualityPartialPlainRegion.lean',
    'lean/MicroCFTA/SourceEqualityClassTarget.lean',
    'lean/MicroCFTA/SourceEqualityAnnotationLanguage.lean',
    'cfta/src/Data/CFTA/Equality/Operations.hs',
    'cfta/src/Data/CFTA/Equality/Constraint.hs',
    'cfta/src/Data/CFTA/Interned/Operations.hs',
    'lean/restart-evidence/20261017-recursive-source-progress/recursive-haskell-boundary-review.md',
    'lean/restart-evidence/20261017-recursive-positional/positional-shape-review.md',
]
reviewed = evidence / 'positional-reviewed-hashes.json'
reviewed.write_text(json.dumps({'review': 'Bounded source and positional-mask investigation', 'entries': [entry(root / name) for name in read_files]}, indent=2) + '\n')
manifest_path = evidence / 'paths-manifest.json'
files = [source, *sorted(p for p in evidence.glob('paths-*') if p.is_file() and p != manifest_path), evidence / 'positional-shape-review.md', reviewed, evidence / 'cap-read-path-build.log']
manifest = {'source_sha256': validation['source_sha256'], 'public_pairs': 20, 'integration_pairs': 6, 'entries': [entry(path) for path in files]}
manifest_path.write_text(json.dumps(manifest, indent=2) + '\n')
print(f"PASS: 20 public pairs; 6 integration pairs; {len(files)} manifest entries")
print(f"source {validation['source_sha256']}")
print(f"manifest {hashlib.sha256(manifest_path.read_bytes()).hexdigest()}")
