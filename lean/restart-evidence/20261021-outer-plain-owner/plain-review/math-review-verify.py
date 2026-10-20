import argparse
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def check(base, item):
    data = (base / item['path']).read_bytes()
    assert len(data) == item['bytes'], ('bytes', item['path'])
    assert hashlib.sha256(data).hexdigest() == item['sha256'], ('sha256', item['path'])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, default=next(
        (p for p in HERE.parents if (p / 'lean/MicroCFTA').is_dir()),
        Path('/home/tritlo/Code/mcfta')))
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    manifest = json.loads((HERE / 'math-review-manifest.json').read_text())
    pins = json.loads((HERE / 'math-review-source-pins.json').read_text())
    for item in manifest['files']:
        check(HERE, item)
    assert manifest['sources'] == pins['sources']
    for item in pins['sources']:
        check(HERE, dict(item, path=item['snapshot']))
        if args.live:
            check(args.root, item)
    assert pins['sources'][0]['sha256'] == 'e464750dced0b7ec8277c59577f474b8bc1ae2a7d5bb40a2b9e6666c8cec0360'
    assert pins['sources'][1]['sha256'] == 'a88a51386f5382b4a3fac5430462331f49a3bd707e7b6d5a3439a41d2df04fdd'
    assert manifest['owned_lean_jobs'] == 0 and manifest['owned_pairs'] == 0
    owner = (HERE / pins['sources'][0]['snapshot']).read_text()
    rows = (HERE / pins['sources'][1]['snapshot']).read_text()
    assert 'SourceCompactGuards.sourceEqualities original.entry.key.constraint = some []' in owner
    assert 'SourceCurrentOuterPlainRowShapes.edge_call parent' in owner
    assert 'SourceCurrentOuterUntouchedProgress.walk_prefix earlierCalls selected' in owner
    assert 'resident_reference_injective' in owner and 'reached.running valid handle owner active' in owner
    assert 'def Origins' in rows and 'theorem initial' in rows and 'theorem edge_call' in rows and 'theorem reached' in rows
    print(json.dumps(dict(status='PASS', pins=len(manifest['files']) + len(pins['sources']),
                          owned_lean_jobs=0, owned_pairs=0, mode='live' if args.live else 'ordinary')))


if __name__ == '__main__':
    main()
