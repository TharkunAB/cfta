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
    manifest = json.loads((HERE / 'filtered-root-review-manifest.json').read_text())
    for item in manifest['entries']:
        path = ROOT / item['path']
        assert path.stat().st_size == item['bytes'], path
        assert sha(path) == item['sha256'], path
    for production in manifest['production']:
        path = ROOT / production['path']
        meta = json.loads((HERE / (production['strict'] + '.json')).read_text())
        assert meta['exit_code'] == 0
        assert not (HERE / meta['log']).read_bytes(), production['strict']
        assert sha(path) == production['sha256'] == sha(HERE / meta['source'])
    for stem in manifest['selected_executions']:
        meta = json.loads((HERE / (stem + '.json')).read_text())
        assert meta['exit_code'] == 0, stem
        assert meta['wrapper'][:5] == [
            '/home/tritlo/Code/heavy-management/bin/capped', '--mem', '4G', '--time', '5m']
        assert json.loads((HERE / meta['limits']).read_text()) == {
            'memory.max': '4294967296',
            'memory.high': '4294967296',
            'memory.swap.max': '0',
        }, stem
        if 'source' in meta:
            assert sha(HERE / meta['source']) == meta['sha256'], stem
    for stem in manifest['canonical']:
        meta = json.loads((HERE / (stem + '.json')).read_text())
        log = (HERE / meta['log']).read_text()
        assert re.search(r'Build completed successfully \(\d+ jobs\)\.', log), stem
        assert not re.search(r'\berror(?:\([^)]*\))?:|sorryAx|failed to pretty print', log), stem
        assert not re.search(
            r'^warning: (?!MicroCFTA/InternedFreshOrdinaryClosedCompletion\.lean:)', log, re.M), stem
    for attempt in manifest['owned_attempts']:
        meta = json.loads((HERE / (attempt['stem'] + '.json')).read_text())
        assert meta['exit_code'] == attempt['exit_code']
        assert sha(HERE / meta['source']) == meta['sha256']
        assert json.loads((HERE / meta['limits']).read_text()) == {
            'memory.max': '4294967296',
            'memory.high': '4294967296',
            'memory.swap.max': '0',
        }
    strict = manifest['constructed_strict']
    meta = json.loads((HERE / (strict + '.json')).read_text())
    assert not (HERE / meta['log']).read_bytes(), strict
    assert sha(HERE / meta['source']) == sha(HERE / 'filtered-root-review-kernels.lean')
    check_group = runpy.run_path(str(HERE / 'verify-probes.py'))['check_group']
    for group in manifest['reused_groups'] + manifest['constructed_groups']:
        check_group(group)
    print(json.dumps({
        'status': 'PASS',
        'entries': len(manifest['entries']),
        'reviewed_production_modules': len(manifest['production']),
        'reused_public_pairs': sum(group['pairs'] for group in manifest['reused_groups']),
        'new_public_pairs': 0,
        'constructed_pairs': sum(group['pairs'] for group in manifest['constructed_groups']),
        'new_production_builds': 0,
        'new_lean_executions': len(manifest['owned_attempts']),
    }, sort_keys=True))


if __name__ == '__main__':
    main()
