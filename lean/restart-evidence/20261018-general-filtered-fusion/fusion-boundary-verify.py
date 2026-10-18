import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
LIMITS = {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    manifest = json.loads((HERE / 'fusion-boundary-manifest.json').read_text())
    for entry in manifest['entries']:
        path = ROOT / entry['path']
        assert path.stat().st_size == entry['bytes'], path
        assert digest(path) == entry['sha256'], path
    for attempt in manifest['attempts']:
        meta = json.loads((HERE / (attempt['name'] + '.json')).read_text())
        assert meta['exit_code'] == attempt['exit_code'], attempt
        assert meta['wrapper'][:5] == ['/home/tritlo/Code/heavy-management/bin/capped', '--mem', '4G', '--time', '5m']
        assert json.loads((HERE / meta['limits']).read_text()) == LIMITS
        assert digest(HERE / meta['source']) == meta['sha256']
    first = (HERE / 'fusion-boundary-search-1.log').read_text()
    partial = (HERE / 'fusion-boundary-small-1.log').read_text()
    final = (HERE / 'fusion-boundary-small-2.log').read_text()
    assert first == '' and final == ''
    assert partial.startswith('(true, true)\n')
    assert 'Inhabited (Syntax Nat Bool)' in partial
    selection = json.loads((HERE / 'fusion-boundary-selection.json').read_text())
    assert selection['finalized'] and selection['status'] == 'INCOMPLETE_SEARCH_NO_COUNTEREXAMPLE'
    assert selection['groups'] == []
    assert selection['public_pairs'] == selection['constructed_pairs'] == selection['reused_public_pairs'] == 0
    assert selection['completed_paired_cases'] == 0
    assert manifest['groups'] == [] and manifest['production'] == []
    print(json.dumps({'status': 'PASS', 'entries': len(manifest['entries']),
        'preserved_attempts': len(manifest['attempts']), 'new_public_pairs': 0,
        'new_constructed_pairs': 0, 'completed_paired_cases': 0,
        'scope': 'incomplete bounded search; two base evaluator facts only; no counterexample'}, sort_keys=True))


if __name__ == '__main__':
    main()
