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
    historical = json.loads((HERE / 'historical-v1.json').read_text())
    v1 = (HERE / historical['path']).read_bytes()
    assert len(v1) == historical['bytes']
    assert hashlib.sha256(v1).hexdigest() == historical['sha256']
    assert historical['v1_manifest_sha256'] == '121a210fe67dbaa802fb751c02ccd9ef16103fc76056901fc5909faf097bc845'
    plan = (HERE / 'plan.md').read_text()
    assert 'Proposed and unproved.' in plan
    assert 'No theorem from this plan has been implemented or checked.' in plan
    assert 'The current goal already authorizes the necessary proof work.' in plan
    assert 'No user permission is required.' in plan
    assert 'new additive public of_written adapter' in plan
    assert 'Then implement one actual capture_source consumer' in plan
    assert 'would need explicit authorization' not in plan
    selection = json.loads((HERE / 'selection.json').read_text())
    assert selection['version'] == 2 and selection['status'] == 'proposed-unproved'
    assert selection['owned_jobs'] == selection['owned_pairs'] == 0
    assert not selection['proofs_implemented'] and not selection['user_permission_required']
    print(json.dumps({'status': 'PASS', 'pins': len(manifest['files']) + len(manifest['sources']),
                      'content_status': 'proposed-unproved-v2', 'owned_jobs': 0, 'owned_pairs': 0,
                      'historical_v1_preserved': True, 'live': args.live}))


if __name__ == '__main__':
    main()
