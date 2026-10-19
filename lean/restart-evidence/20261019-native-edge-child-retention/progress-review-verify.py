import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    pins = json.loads((HERE / 'progress-review-source-pins.json').read_text())['files']
    for item in pins:
        path = ROOT / item['path']
        assert path.stat().st_size == item['bytes'], item['path']
        assert digest(path) == item['sha256'], item['path']
    selection = json.loads((HERE / 'progress-review-selection.json').read_text())
    for stem in selection['strict']:
        meta = json.loads((HERE / (stem + '.json')).read_text())
        assert meta['exit_code'] == 0, stem
        assert not (HERE / meta['log']).read_bytes(), stem
    for stem in selection['canonical']:
        meta = json.loads((HERE / (stem + '.json')).read_text())
        assert meta['exit_code'] == 0, stem
        assert 'Build completed successfully' in (HERE / meta['log']).read_text(), stem
    for group in selection['groups']:
        meta = json.loads((HERE / (group['name'] + '.json')).read_text())
        assert meta['exit_code'] == 0, group['name']
    print(json.dumps({'status': 'PASS', 'pins': len(pins), 'owned_lean_runs': 0,
                      'owned_public_pairs': 0, 'reused_public_pairs': 8,
                      'owned_constructed_pairs': 0, 'reused_constructed_pairs': 1}))


if __name__ == '__main__':
    main()
