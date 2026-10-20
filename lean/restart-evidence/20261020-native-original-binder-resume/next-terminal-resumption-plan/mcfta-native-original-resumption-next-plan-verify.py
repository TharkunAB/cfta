import argparse
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
PREFIX = 'mcfta-native-original-resumption-next-plan'


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, default=Path('/home/tritlo/Code/mcfta'))
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    manifest = json.loads((HERE / (PREFIX + '-manifest.json')).read_text())
    for base, entries in [(HERE, manifest['files']), (args.root, manifest['sources'])]:
        for entry in entries:
            data = (base / entry['path']).read_bytes()
            assert len(data) == entry['bytes'], entry['path']
            assert hashlib.sha256(data).hexdigest() == entry['sha256'], entry['path']
    pins = json.loads((HERE / (PREFIX + '-source-pins.json')).read_text())
    assert pins['files'] == manifest['sources']
    plan = (HERE / (PREFIX + '.md')).read_text()
    for expected in ['Design only.', 'No theorem in this note has been implemented or checked.',
                     'of_observed once', 'SyntaxBound', 'same five', 'sourceHeap',
                     'does not close a global renewal rank']:
        assert expected in plan, expected
    print(json.dumps({'status': 'PASS', 'pins': len(manifest['files']) + len(manifest['sources']),
                      'kind': 'unproved-design', 'lean_jobs': 0, 'proof_pairs': 0, 'live': args.live}))


if __name__ == '__main__':
    main()
