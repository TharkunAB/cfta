import hashlib
import json
import re
import runpy
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
PREFIX = 'open-language-review'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    manifest = json.loads((HERE / (PREFIX + '-manifest.json')).read_text())
    for item in manifest['entries']:
        path = ROOT / item['path']
        assert path.stat().st_size == item['bytes'], path
        assert sha(path) == item['sha256'], path
    for stem in manifest['selected_executions']:
        meta = json.loads((HERE / (stem + '.json')).read_text())
        assert meta['exit_code'] == 0, stem
        assert meta['wrapper'][:5] == [
            '/home/tritlo/Code/heavy-management/bin/capped',
            '--mem', '4G', '--time', '5m',
        ], stem
        assert json.loads((HERE / meta['limits']).read_text()) == {
            'memory.max': '4294967296',
            'memory.high': '4294967296',
            'memory.swap.max': '0',
        }, stem
        if 'source' in meta:
            assert sha(HERE / meta['source']) == meta['sha256'], stem
    production = manifest['production']
    strict = json.loads((HERE / (production['strict'] + '.json')).read_text())
    assert not (HERE / strict['log']).read_bytes()
    assert sha(ROOT / production['path']) == production['sha256']
    assert sha(HERE / strict['source']) == production['sha256']
    canonical = json.loads((HERE / (production['canonical'] + '.json')).read_text())
    log = (HERE / canonical['log']).read_text()
    assert re.search(r'Build completed successfully \(568 jobs\)\.', log)
    assert not re.search(r'\b(?:warning|error)(?:\([^)]*\))?:|sorryAx|failed to pretty print', log)
    fixture = json.loads((HERE / (manifest['constructed_strict'] + '.json')).read_text())
    assert not (HERE / fixture['log']).read_bytes()
    assert fixture['sha256'] == manifest['fixture_sha256']
    check_group = runpy.run_path(str(HERE / (PREFIX + '-probes.py')))['check_group']
    for group in manifest['reused_groups']:
        check_group(group)
    assert sha(HERE / 'open-binder-simulation-manifest.json') == manifest['previous_manifest_sha256']
    print(json.dumps({
        'status': 'PASS',
        'entries': len(manifest['entries']),
        'reviewed_production_modules': 1,
        'reused_public_pairs': 3,
        'reused_constructed_pairs': 2,
        'new_public_pairs': 0,
        'new_constructed_pairs': 0,
        'new_lean_executions': 0,
    }, sort_keys=True))


if __name__ == '__main__':
    main()
