"""Check immutable source snapshots and the reused optional-prefix receipts."""
import argparse
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
DEFAULT_ROOT = next((p for p in HERE.parents if (p / 'lean/MicroCFTA').is_dir()), Path('/home/tritlo/Code/mcfta'))
HEADS = ['MicroCFTA.SourceCurrentNativeQueryOptionalPrefix.node', 'MicroCFTA.SourceCurrentNativeQueryOptionalPrefix.edge']
OPTIONS = ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
           'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_text())


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, default=DEFAULT_ROOT)
    parser.add_argument('--live-root', '--live', action='store_true')
    args = parser.parse_args()
    manifest = read(HERE / 'manifest.json')
    assert len({item['path'] for item in manifest['files']}) == len(manifest['files'])
    for item in manifest['files']:
        relative = Path(item['path'])
        assert not relative.is_absolute() and '..' not in relative.parts
        path = HERE / relative
        assert path.stat().st_size == item['bytes'] and sha(path) == item['sha256'], str(relative)
    sources = read(HERE / 'source-pins.json')
    for item in sources['sources']:
        snapshot = HERE / item['snapshot']
        assert snapshot.stat().st_size == item['bytes'] and sha(snapshot) == item['sha256']
        if args.live_root:
            assert sha(args.root / item['path']) == item['sha256'], item['path']
    candidate = HERE / sources['candidate']['path']
    assert sha(candidate) == sources['candidate']['sha256'] == '01216fbec107424e43905359d209cb7fa56e9a2fefb7f7d8be87883d09d3fc4e'
    selected = read(HERE / 'selection.json')
    assert selected['strict'] == 'query-prefix-direct-3'
    assert selected['public'] == 'query-prefix-public-1'
    assert selected['new_lean_jobs'] == selected['new_proof_pairs'] == 0
    assert selected['public_heads'] == HEADS and selected['reused_public_pairs'] == 2
    for stem in ['query-prefix-direct-3', 'query-prefix-public-1']:
        meta = read(HERE / 'receipts' / (stem + '.json'))
        assert meta['exit_code'] == 0
        assert meta['command'][0] == '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean'
        assert '-Dlinter.all=true' in meta['command']
        assert meta['wrapper'][meta['wrapper'].index('--mem') + 1] == '4G'
        assert meta['wrapper'][meta['wrapper'].index('--time') + 1] == '5m'
        assert read(HERE / 'receipts' / meta['limits']) == {
            'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
        source = HERE / 'receipts' / meta['source']
        assert sha(source) == meta['sha256']
        usage = read(HERE / 'receipts' / (stem + '.usage.json'))
        assert usage['age_seconds'] < 120 and usage['remaining_percent'] > 1
        log = (HERE / 'receipts' / meta['log']).read_text()
        if stem.endswith('direct-3'):
            assert not log and source.read_bytes() == candidate.read_bytes()
        else:
            text = source.read_text()
            assert source.read_bytes().startswith(candidate.read_bytes())
            for option in OPTIONS:
                assert 'set_option ' + option in text
            assert re.findall(r'^#check @([^\s]+)', text, re.M) == HEADS
            assert re.findall(r'^#print (?!axioms )([^\s]+)', text, re.M) == HEADS
            assert re.findall(r'^#print axioms ([^\s]+)', text, re.M) == HEADS
            for head in HEADS:
                assert re.search(r'theorem ' + re.escape(head) + r'(?:\.\{[^}]*\})?\s*:', log)
            assert ':=' in log
            assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|maximum recursion depth|⋯|…|\.\.\.', log)
            reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log)
            assert [name for name, _ in reports] == HEADS
            for _name, actual_axioms in reports:
                axioms = re.sub(r'\.\{[^}]*\}', '', actual_axioms)
                assert set(re.split(r',\s*', axioms.strip())) <= {'propext', 'Classical.choice', 'Quot.sound'}
    print(json.dumps({'status': 'PASS', 'live_root': args.live_root,
        'manifest_files': len(manifest['files']), 'root_foundations': len(sources['sources']),
        'reused_checked_public_pairs': 2, 'new_lean_jobs': 0, 'new_proof_pairs': 0}))


if __name__ == '__main__':
    main()
