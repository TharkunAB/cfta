import hashlib
import json
import re
import runpy
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    manifest = json.loads((HERE / 'origin-exposure-manifest.json').read_text())
    for item in manifest['entries']:
        path = ROOT / item['path']
        assert path.stat().st_size == item['bytes'], path
        assert sha(path) == item['sha256'], path
    selection = json.loads((HERE / 'origin-exposure-selection.json').read_text())
    assert selection['status'] == 'final'
    production = ROOT / selection['production']
    for stem in [selection['strict'], selection['constructed_strict']]:
        meta = json.loads((HERE / (stem + '.json')).read_text())
        assert meta['exit_code'] == 0
        assert not (HERE / meta['log']).read_bytes(), stem
        assert sha(HERE / meta['source']) == meta['sha256']
    strict = json.loads((HERE / (selection['strict'] + '.json')).read_text())
    assert sha(production) == strict['sha256']
    for stem in selection['executions']:
        meta = json.loads((HERE / (stem + '.json')).read_text())
        assert meta['exit_code'] == 0
        assert meta['wrapper'][:5] == [
            '/home/tritlo/Code/heavy-management/bin/capped', '--mem', '4G', '--time', '5m']
        assert json.loads((HERE / meta['limits']).read_text()) == {
            'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
        assert meta['command'][0].startswith(
            '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/')
        if 'source' in meta:
            assert sha(HERE / meta['source']) == meta['sha256']
    meta = json.loads((HERE / (selection['canonical'] + '.json')).read_text())
    log = (HERE / meta['log']).read_text()
    assert re.search(r'Build completed successfully \(\d+ jobs\)\.', log)
    assert not re.search(r'\berror(?:\([^)]*\))?:|sorryAx|failed to pretty print', log)
    assert not re.search(r'^warning: (?!MicroCFTA/InternedFreshOrdinaryClosedCompletion\.lean:)', log, re.M)
    check_group = runpy.run_path(str(HERE / 'verify-probes.py'))['check_group']
    for group in selection['groups']:
        check_group(group)
    print(json.dumps({
        'status': 'PASS', 'entries': len(manifest['entries']),
        'public_pairs': sum(group['pairs'] for group in selection['groups'] if group['kind'] == 'new-public'),
        'constructed_pairs': sum(group['pairs'] for group in selection['groups'] if group['kind'] == 'constructed'),
        'strict_logs_zero_bytes': 2,
    }, sort_keys=True))


if __name__ == '__main__':
    main()
