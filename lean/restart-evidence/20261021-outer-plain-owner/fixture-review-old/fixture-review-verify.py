import argparse
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCE = '5f2970b648910fd2b3a7927a776b7c8733ab4c6ffad27f1832291793b99a14de'


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
    manifest = json.loads((HERE / 'fixture-review-manifest.json').read_text())
    pins = json.loads((HERE / 'fixture-review-source-pins.json').read_text())
    for item in manifest['files']:
        check(HERE, item)
    assert manifest['sources'] == pins['sources']
    for item in pins['sources']:
        check(HERE, dict(item, path=item['snapshot']))
        if args.live:
            check(args.root, item)
    assert pins['sources'][0]['sha256'] == SOURCE
    assert pins['sources'][1]['sha256'] == 'e464750dced0b7ec8277c59577f474b8bc1ae2a7d5bb40a2b9e6666c8cec0360'
    assert pins['sources'][2]['sha256'] == 'a88a51386f5382b4a3fac5430462331f49a3bd707e7b6d5a3439a41d2df04fdd'
    source = (HERE / 'inputs/PlainOwnerFixture.lean').read_text()
    strict = json.loads((HERE / 'inputs/fixture-strict-4.json').read_text())
    assert strict['exit_code'] == 0 and strict['sha256'] == SOURCE
    assert strict['command'][0] == '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean'
    assert '-Dlinter.all=true' in strict['command']
    assert (HERE / 'inputs/fixture-strict-4.source.lean').read_text() == source
    assert not (HERE / 'inputs/fixture-strict-4.log').read_bytes()
    assert json.loads((HERE / 'inputs/fixture-strict-4.limits.json').read_text()) == {
        'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
    assert strict['wrapper'][strict['wrapper'].index('--mem') + 1] == '4G'
    assert strict['wrapper'][strict['wrapper'].index('--time') + 1] == '5m'
    usage = json.loads((HERE / 'inputs/fixture-strict-4.usage.json').read_text())
    assert usage['age_seconds'] < 120 and usage['remaining_percent'] > 1
    assert source.count('SourceCurrentOuterPlainOwnerProgress.dispatch') == 1
    for token in ['private noncomputable def cold := edgeCall',
                  'private noncomputable def warmed := cold.state',
                  'private noncomputable def running := (beginNode owner warmed).2.2',
                  'SourceCurrentOuterPlainRowShapes.edge_call cold_return',
                  '(row.children.take 1)', 'private theorem earlier_return : earlier = .done [selected] earlier.state',
                  'theorem actual_warm_plain_dispatch :',
                  '(beginEdge ⟨inherited,row⟩ running).2.1 = .ready row',
                  'dispatch.2.nodeResults.cells 0 = some ⟨owner,.evaluating⟩',
                  'selected.referenceOf ≠ root.referenceOf',
                  '(NodeRequest.mk dispatch.1 selected).key ≠ owner.key']:
        assert token in source, token
    assert manifest['owned_lean_jobs'] == 0 and manifest['owned_pairs'] == 0
    assert manifest['reused_selected_strict'] == 1 and manifest['reused_selected_public'] == 0
    print(json.dumps(dict(status='PASS', pins=len(manifest['files']) + len(pins['sources']),
                          owned_lean_jobs=0, owned_pairs=0, reused_selected_strict=1,
                          mode='live' if args.live else 'ordinary')))


if __name__ == '__main__':
    main()
