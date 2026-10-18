import hashlib
import importlib.util
import json
import re
from pathlib import Path


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    manifest = json.loads((HERE / 'guard-uniform-review-manifest.json').read_text())
    for item in manifest['entries']:
        path = ROOT / item['path']
        assert path.is_file(), path
        assert path.stat().st_size == item['bytes'], path
        assert sha(path) == item['sha256'], path
    spec = importlib.util.spec_from_file_location('review_probe_checks', HERE / 'verify-probes.py')
    checks = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checks)
    for group in manifest['reviewed_groups']:
        checks.check_group(group)
        meta = json.loads((HERE / (group['name'] + '.json')).read_text())
        source = (HERE / meta['source']).read_text()
        names = re.findall(r'^#check @([^\s]+)', source, re.M)
        assert len(names) == len(set(names)) == group['pairs']
        assert re.findall(r'^#print (?!axioms )([^\s]+)', source, re.M) == names
        assert re.findall(r'^#print axioms ([^\s]+)', source, re.M) == names
    for module in manifest['production']:
        strict = json.loads((HERE / (module['strict'] + '.json')).read_text())
        assert sha(ROOT / module['path']) == module['sha256'] == sha(HERE / strict['source'])
        assert (HERE / strict['log']).stat().st_size == 0, module['strict']
        canonical = json.loads((HERE / (module['canonical'] + '.json')).read_text())
        assert canonical['command'][-1] == 'MicroCFTA.' + Path(module['path']).stem
        assert re.search(r'Build completed successfully \(\d+ jobs\)\.', (HERE / canonical['log']).read_text())
    for stem in manifest['selected_executions']:
        meta = json.loads((HERE / (stem + '.json')).read_text())
        assert meta['exit_code'] == 0, stem
        assert meta['wrapper'][:5] == [
            '/home/tritlo/Code/heavy-management/bin/capped', '--mem', '4G', '--time', '5m',
        ], stem
        assert json.loads((HERE / meta['limits']).read_text()) == {
            'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0',
        }, stem
        if 'source' in meta:
            assert sha(HERE / meta['source']) == meta['sha256'], stem
    print(json.dumps({
        'status': 'PASS', 'entries': len(manifest['entries']),
        'reviewed_public_pairs': 15, 'new_public_pairs': 0,
        'new_constructed_pairs': 0, 'new_lean_runs': 0,
    }, sort_keys=True))


if __name__ == '__main__':
    main()
