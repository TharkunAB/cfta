import argparse
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, default=Path('/home/tritlo/Code/mcfta'))
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    manifest = json.loads((HERE / 'manifest.json').read_text())
    for base, entries in [(HERE, manifest['files']), (args.root, manifest['sources'])]:
        for entry in entries:
            data = (base / entry['path']).read_bytes()
            assert len(data) == entry['bytes'], entry['path']
            assert hashlib.sha256(data).hexdigest() == entry['sha256'], entry['path']
    prefix = args.root / 'lean/restart-evidence/20261020-native-capture-leaf-producers/root-active-production-strict-1'
    meta = json.loads(prefix.with_suffix('.json').read_text())
    assert meta['exit_code'] == 0
    assert not prefix.with_suffix('.log').read_bytes()
    assert (HERE / 'reviewed-production.lean').read_bytes() == prefix.with_suffix('.source.lean').read_bytes()
    assert json.loads(prefix.with_suffix('.limits.json').read_text()) == {
        'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
    assert meta['wrapper'][meta['wrapper'].index('--mem') + 1] == '4G'
    assert meta['wrapper'][meta['wrapper'].index('--time') + 1] == '5m'
    usage = json.loads(prefix.with_suffix('.usage.json').read_text())
    assert usage['remaining_percent'] > 1 and usage['age_seconds'] < 120
    selection = json.loads((HERE / 'selection.json').read_text())
    assert selection['owned_jobs'] == 0 and selection['owned_pairs'] == 0
    assert selection['reviewed_source_heads'] == 7
    print(json.dumps({'status': 'PASS', 'pins': len(manifest['files']) + len(manifest['sources']),
                      'owned_jobs': 0, 'owned_pairs': 0, 'reused_strict_receipts': 1,
                      'reviewed_source_heads': 7, 'live': args.live}))


if __name__ == '__main__':
    main()
