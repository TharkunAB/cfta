import hashlib
import json
from pathlib import Path


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def main() -> None:
    manifest = json.loads((HERE / 'normality-reuse-manifest.json').read_text())
    assert manifest['owned_lean_runs'] == 0
    assert manifest['owned_proof_pairs'] == 0
    assert manifest['reused_proof_pairs'] == 0
    assert manifest['production_changes'] == []
    paths = [item['path'] for item in manifest['files']]
    assert len(paths) == len(set(paths))
    for item in manifest['files']:
        path = ROOT / item['path']
        payload = path.read_bytes()
        assert len(payload) == item['bytes'], item['path']
        assert hashlib.sha256(payload).hexdigest() == item['sha256'], item['path']
        assert path.suffix in {'.lean', '.md', '.py', '.json'}, item['path']
    selection = json.loads((HERE / 'normality-reuse-selection.json').read_text())
    assert selection['finalized']
    assert selection['groups'] == []
    assert selection['owned_lean_runs'] == 0
    assert selection['owned_proof_pairs'] == 0
    print(json.dumps({
        'status': 'PASS',
        'manifest_pins': len(paths),
        'owned_lean_runs': 0,
        'owned_proof_pairs': 0,
        'reused_proof_pairs': 0,
        'production_changes': [],
    }, indent=2))


if __name__ == '__main__':
    main()
