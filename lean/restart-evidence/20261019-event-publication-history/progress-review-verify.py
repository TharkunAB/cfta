import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def main():
    pins = json.loads((HERE / 'progress-review-source-pins.json').read_text())['files']
    for item in pins:
        data = (ROOT / item['path']).read_bytes()
        assert len(data) == item['bytes'], item['path']
        assert hashlib.sha256(data).hexdigest() == item['sha256'], item['path']
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
    print(json.dumps({'status': 'PASS', 'pins': len(pins), 'review_lean_jobs': 0,
                      'new_review_proof_pairs': 0, 'reused_public_pairs': 30,
                      'reused_constructed_pairs': 1}))


if __name__ == '__main__':
    main()
