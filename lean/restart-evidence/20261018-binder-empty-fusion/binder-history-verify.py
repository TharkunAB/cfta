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
    manifest = json.loads((HERE / 'binder-history-manifest.json').read_text())
    for entry in manifest['entries']:
        path = ROOT / entry['path']
        assert path.stat().st_size == entry['bytes'], path
        assert sha(path) == entry['sha256'], path
    selected = json.loads((HERE / 'binder-history-selection.json').read_text())
    assert selected['finalized'] and not selected['production']
    assert selected['public_pairs'] == selected['reused_public_pairs'] == 0
    assert selected['constructed_pairs'] == 1
    assert not selected['full_contract_verified'] and not selected['counterexample']
    for attempt in selected['attempts']:
        meta = json.loads((HERE / (attempt['name'] + '.json')).read_text())
        assert meta['exit_code'] == attempt['exit_code'], attempt
        assert meta['wrapper'][:5] == ['/home/tritlo/Code/heavy-management/bin/capped', '--mem', '4G', '--time', '5m']
        assert json.loads((HERE / meta['limits']).read_text()) == LIMITS
        assert sha(HERE / meta['source']) == meta['sha256']
    strict = json.loads((HERE / (selected['constructed_strict'] + '.json')).read_text())
    assert strict['exit_code'] == 0 and not (HERE / strict['log']).read_bytes()
    assert sha(HERE / strict['source']) == sha(HERE / 'binder-history-projections.lean')
    spec = importlib.util.spec_from_file_location('binder_history_probe_check', HERE / 'binder-history-probe-check.py')
    probes = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(probes)
    for group in selected['groups']:
        probes.check_group(group)
    log = (HERE / 'binder-history-staged-3.log').read_text()
    assert log.splitlines() == [
        'outer: (true, 13, 9)', 'outer-names: (8, 1)',
        'older-used: (11, 6, true, true)',
        'first-probes: (true, true, true, true, true)',
        'second-probes: (true, true, true, true, true)',
        'current-requests: (true, true, true, true, true)',
        'first-empty: (true, true, 14, 12)', 'second-empty: (true, true, 14, 12)']
    assert not (HERE / 'binder-history-kernels-1.log').read_bytes()
    source = (HERE / strict['source']).read_text()
    assert 'private theorem checked_witness :' in source
    assert ' := checked_witness' in source
    assert 'private theorem computed : checks = true := by cbv' in source
    assert 'Bool.and_eq_true_iff.mp computed' in source
    assert manifest['groups'] == selected['groups']
    print(json.dumps({'status': 'PASS', 'entries': len(manifest['entries']),
        'preserved_attempts': len(selected['attempts']), 'new_public_pairs': 0,
        'new_constructed_pairs': 1, 'full_contract_verified': False,
        'counterexample': False}, sort_keys=True))


if __name__ == '__main__':
    main()
