import hashlib
import importlib.util
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
LIMITS = {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    manifest = json.loads((HERE / 'profile-contract-integration-manifest.json').read_text())
    for entry in manifest['entries']:
        path = ROOT / entry['path']
        assert path.stat().st_size == entry['bytes'], path
        assert sha(path) == entry['sha256'], path
    selected = json.loads((HERE / 'profile-contract-integration-selection.json').read_text())
    assert selected['finalized'] and selected['public_pairs'] == 0
    assert selected['constructed_pairs'] == 1 and selected['reused_public_pairs'] == 3
    for stem in selected['receipts']:
        meta = json.loads((HERE / (stem + '.json')).read_text())
        assert meta['exit_code'] == 0, stem
        assert json.loads((HERE / meta['limits']).read_text()) == LIMITS
        if 'source' in meta:
            assert sha(HERE / meta['source']) == meta['sha256']
    for stem in [selected['strict'], selected['reviewed_strict']]:
        assert not (HERE / (stem + '.log')).read_bytes(), stem
    canonical = (HERE / (selected['reviewed_canonical'] + '.log')).read_text()
    assert 'Build completed successfully (595 jobs).' in canonical
    assert 'warning:' not in canonical and 'error:' not in canonical
    assert sha(ROOT / selected['reviewed_production']) == selected['reviewed_sha256']
    reviewed_strict = json.loads((HERE / (selected['reviewed_strict'] + '.json')).read_text())
    assert reviewed_strict['sha256'] == selected['reviewed_sha256']
    strict = json.loads((HERE / (selected['strict'] + '.json')).read_text())
    assert sha(HERE / 'profile-contract-integration-kernels.lean') == strict['sha256']
    source = (HERE / strict['source']).read_text()
    private_statement = source.split('private theorem checked_witness :', 1)[1].split(' := by\n  refine ⟨actual_done', 1)[0]
    public_statement = source.split('theorem installed_parametric_contract :', 1)[1].split(' := checked_witness', 1)[0]
    assert private_statement == public_statement
    assert 'SourceCurrentStoredProfileFunction.congr' in source
    assert source.count('SourceCurrentStoredReconstruction.execute') == 2
    assert 'SourceCurrentStoredMuProfileContract.execute' in source
    assert 'root.free = [] ∧ root.referenceOf ≠ .empty' in source
    assert 'environment (.uninterned 99) = some (.reference (.uninterned 88))' in source
    spec = importlib.util.spec_from_file_location('profile_contract_integration_probes', HERE / 'profile-contract-integration-probe-check.py')
    probes = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(probes)
    for group in selected['groups'] + selected['reviewed_groups']:
        probes.check_group(group)
    assert manifest['groups'] == selected['groups']
    print(json.dumps({'status': 'PASS', 'entries': len(manifest['entries']),
        'public_pairs': 0, 'constructed_pairs': 1, 'reused_public_pairs': 3,
        'retained_warning_attempts': 2,
        'scope': 'actual installed smart-unused live-capture contract and constructed sequential substitutions; general publication contract remains open'}, sort_keys=True))


if __name__ == '__main__':
    main()
