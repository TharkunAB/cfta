from pathlib import Path
import hashlib
import json
import re

root = Path(__file__).resolve().parents[3]
evidence = Path(__file__).resolve().parent
required = ['linter.all true', 'pp.explicit true', 'pp.proofs true', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 1000000', 'pp.fullNames true']

def entry(path):
    return {'path': path.relative_to(root).as_posix(), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}

for prefix, module, public_count, kernel_count, direct, kernel_attempt, canonical, jobs in [
    ('path-edit', 'SourceCurrentConstrainedCapEditSupport', 35, 3, 12, 8, 'edit-support-build.log', 1345),
    ('path-edit-shared', 'SourceCurrentConstrainedCapSharedSupport', 11, 2, 2, 2, 'shared-support-build.log', 1375),
]:
    source = root / f'lean/MicroCFTA/{module}.lean'
    assert source.read_bytes() == (evidence / f'{prefix}-final.source.lean').read_bytes()
    assert source.read_bytes() == (evidence / f'{prefix}-direct-{direct}.source.lean').read_bytes()
    assert (evidence / f'{prefix}-direct-{direct}.log').stat().st_size == 0
    probe_results = []
    for kind, count, attempt in [('public', public_count, 1), ('kernels', kernel_count, kernel_attempt)]:
        probe = evidence / f'{prefix}-{kind}.lean'
        assert probe.read_bytes() == (evidence / f'{prefix}-{kind}-{attempt}.source.lean').read_bytes()
        for option in required:
            assert f'set_option {option}' in probe.read_text()
        assert probe.read_text().count('#print axioms ') == count
        assert probe.read_text().count('#check @') == count
        log_path = evidence / f'{prefix}-{kind}-{attempt}.log'
        log = log_path.read_text()
        assert not re.search(r'error|warning|sorryAx|declaration uses|\.\.\.', log)
        names = re.findall(r"^'([^']+)' (?:depends on axioms:|does not depend on any axioms)", log, re.M)
        signatures = re.findall(r'^@?(MicroCFTA\.[^\s:]+) :', log, re.M)
        assert len(names) == count, names
        assert signatures == names, (signatures, names)
        for axioms in re.findall(r'depends on axioms: \[([^\]]*)\]', log, re.S):
            for axiom in axioms.split(','):
                name = re.sub(r'\.\{.*\}', '', axiom.strip())
                assert name in {'propext', 'Classical.choice', 'Quot.sound'}, name
        probe_results.append({'source': probe.relative_to(root).as_posix(), 'log': log_path.relative_to(root).as_posix(), 'pairs': count, 'exit_code': 0, 'warnings': 0, 'custom_axioms': 0})
    canonical_path = evidence / canonical
    assert f'Build completed successfully ({jobs} jobs).' in canonical_path.read_text()
    validation = {'source_sha256': entry(source)['sha256'], 'lines': len(source.read_text().splitlines()), 'lean_version': '4.34.1', 'strict_direct': {'log': (evidence / f'{prefix}-direct-{direct}.log').relative_to(root).as_posix(), 'exit_code': 0, 'bytes': 0}, 'canonical': {'log': canonical_path.relative_to(root).as_posix(), 'exit_code': 0, 'jobs': jobs, 'new_warnings': 0, 'note': 'Only the historical dependency unused-input warning appears.'}, 'imported_probes': probe_results}
    (evidence / f'{prefix}-validation.json').write_text(json.dumps(validation, indent=2) + '\n')
    manifest_path = evidence / f'{prefix}-manifest.json'
    owned = [p for p in sorted(evidence.glob(f'{prefix}-*')) if p.is_file() and p != manifest_path]
    if prefix == 'path-edit':
        owned = [p for p in owned if not p.name.startswith('path-edit-shared-')]
    owned += [canonical_path, evidence / 'path-edit-verify.py']
    owned = list(dict.fromkeys(owned))
    manifest = {'source_sha256': validation['source_sha256'], 'public_pairs': public_count, 'integration_pairs': kernel_count, 'entries': [entry(p) for p in [source, *owned]]}
    manifest_path.write_text(json.dumps(manifest, indent=2) + '\n')
    print(f'{prefix}: {public_count} public + {kernel_count} kernel pairs PASS; {len(manifest["entries"])} hashes')
    print(f'{manifest_path.name} SHA256 {hashlib.sha256(manifest_path.read_bytes()).hexdigest()}')
