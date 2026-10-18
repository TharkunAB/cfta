import hashlib
import json
import re
import runpy
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
PREFIX = 'source-directed'
LIMITS = {
    'memory.max': '4294967296',
    'memory.high': '4294967296',
    'memory.swap.max': '0',
}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def receipt(stem, expected=0):
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert meta['exit_code'] == expected, stem
    assert meta['wrapper'][:5] == [
        '/home/tritlo/Code/heavy-management/bin/capped',
        '--mem', '4G', '--time', '5m',
    ], stem
    assert json.loads((HERE / meta['limits']).read_text()) == LIMITS, stem
    if 'source' in meta:
        assert sha(HERE / meta['source']) == meta['sha256'], stem
    return meta


def main():
    manifest = json.loads((HERE / (PREFIX + '-manifest.json')).read_text())
    for item in manifest['entries']:
        path = ROOT / item['path']
        assert path.stat().st_size == item['bytes'], path
        assert sha(path) == item['sha256'], path
    for stem in manifest['selected_executions']:
        receipt(stem)
    for production in manifest['production']:
        strict = receipt(production['strict'])
        assert not (HERE / strict['log']).read_bytes(), production['strict']
        assert sha(ROOT / production['path']) == production['sha256']
        assert sha(HERE / strict['source']) == production['sha256']
        canonical = receipt(production['canonical'])
        log = (HERE / canonical['log']).read_text()
        assert re.search(r'Build completed successfully \(\d+ jobs\)\.', log), production['canonical']
        assert not re.search(r'\berror(?:\([^)]*\))?:|sorryAx|failed to pretty print', log)
        assert not re.search(
            r'^warning: (?!MicroCFTA/InternedFreshOrdinaryClosedCompletion\.lean:24:5:)', log, re.M)
    for attempt in manifest['owned_attempts']:
        receipt(attempt['stem'], attempt['exit_code'])
    strict = receipt(manifest['constructed_strict'])
    assert not (HERE / strict['log']).read_bytes()
    assert sha(HERE / strict['source']) == sha(HERE / (PREFIX + '-kernels.lean'))
    check_group = runpy.run_path(str(HERE / (PREFIX + '-probes.py')))['check_group']
    for group in manifest['groups'] + manifest['reused_groups']:
        check_group(group)
    selection = json.loads((HERE / (PREFIX + '-selection.json')).read_text())
    assert selection['finalized']
    assert selection['groups'] == manifest['groups']
    print(json.dumps({
        'status': 'PASS',
        'entries': len(manifest['entries']),
        'new_production_modules': 1,
        'reviewed_other_modules': 1,
        'new_public_pairs': 10,
        'new_constructed_pairs': 1,
        'reused_public_pairs': 2,
        'owned_lean_executions': len(manifest['owned_attempts']),
    }, sort_keys=True))


if __name__ == '__main__':
    main()
