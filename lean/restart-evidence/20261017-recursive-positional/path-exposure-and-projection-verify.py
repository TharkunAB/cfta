from pathlib import Path
import hashlib
import json
import re

root = Path(__file__).resolve().parents[3]
evidence = root / 'lean/restart-evidence/20261017-recursive-positional'

def entry(path: Path) -> dict[str, str]:
    return {'path': path.relative_to(root).as_posix(), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}

required_options = ['linter.all true', 'pp.explicit true', 'pp.proofs true', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 1000000', 'pp.fullNames true']
for prefix, module, public_count, kernel_count, kernel_log, canonical_jobs, note in [
    ('path-exposure', 'SourceCurrentConstrainedCapPathExposure', 5, 3, 1, 1085, 'path-exposure-review.md'),
    ('supported-projection', 'SourceCurrentConstrainedCapSupportedProjection', 4, 2, 3, 1088, 'supported-projection-independent-review.md'),
]:
    source = root / f'lean/MicroCFTA/{module}.lean'
    assert source.read_bytes() == (evidence / f'{prefix}-final.source.lean').read_bytes()
    probe_results = []
    for kind, count, attempt in [('public', public_count, 1), ('kernels', kernel_count, kernel_log)]:
        probe = evidence / f'{prefix}-{kind}.lean'
        snapshot = evidence / f'{prefix}-{kind}-{attempt}.source.lean'
        assert probe.read_bytes() == snapshot.read_bytes()
        for option in required_options:
            assert f'set_option {option}' in probe.read_text()
        path = evidence / f'{prefix}-{kind}-{attempt}.log'
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
        probe_results.append({'source': probe.relative_to(root).as_posix(), 'log': path.relative_to(root).as_posix(), 'pairs': count, 'exit_code': 0, 'warnings': 0, 'custom_axioms': 0})
    canonical = evidence / f'{prefix}-build.log'
    assert f'Build completed successfully ({canonical_jobs} jobs).' in canonical.read_text()
    validation = {'source_sha256': entry(source)['sha256'], 'lean_version': '4.34.1', 'canonical': {'log': canonical.relative_to(root).as_posix(), 'jobs': canonical_jobs, 'exit_code': 0, 'new_warnings': 0}, 'imported_probes': probe_results}
    if prefix == 'path-exposure':
        direct = evidence / 'path-exposure-direct-3.log'
        assert direct.stat().st_size == 0
        assert source.read_bytes() == (evidence / 'path-exposure-direct-3.source.lean').read_bytes()
        validation['strict_direct'] = {'log': direct.relative_to(root).as_posix(), 'bytes': 0, 'exit_code': 0}
    (evidence / f'{prefix}-validation.json').write_text(json.dumps(validation, indent=2) + '\n')
    manifest_path = evidence / f'{prefix}-manifest.json'
    files = [source, *sorted(p for p in evidence.glob(f'{prefix}-*') if p.is_file() and p != manifest_path), evidence / note, evidence / 'path-exposure-and-projection-verify.py']
    files = list(dict.fromkeys(files))
    if prefix == 'supported-projection':
        files += [root / 'lean/MicroCFTA/SourceCurrentConstrainedCapProjection.lean', root / 'lean/MicroCFTA/SourceCurrentConstrainedCapPathExposure.lean', root / 'lean/MicroCFTA/SourceCurrentConstrainedCapPaths.lean']
    manifest = {'source_sha256': validation['source_sha256'], 'public_pairs': public_count, 'integration_pairs': kernel_count, 'entries': [entry(path) for path in files]}
    manifest_path.write_text(json.dumps(manifest, indent=2) + '\n')
    print(f'{prefix}: {public_count} public, {kernel_count} integration, {len(files)} manifest entries PASS')
    print(f'manifest {hashlib.sha256(manifest_path.read_bytes()).hexdigest()}')
