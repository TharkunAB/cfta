"""Verify the reviewed owner/Mu snapshots and their existing selected receipts."""
import argparse
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
DEFAULT_ROOT = next((p for p in HERE.parents if (p / 'lean/MicroCFTA').is_dir()), Path('/home/tritlo/Code/mcfta'))
OPTIONS = ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
           'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']
EXPECTED = {'SourceCurrentNativeOptionalOwnerReceipt.lean': '51afa87833183f19c4a488f973767465bd05765ffa5973e1114f9c7496f9a7f8',
            'SourceCurrentNativeMuOptionalPrefix.lean': 'ca22ede9e6ccf3699f9aa6297d06cc24ba6661d14fb04a4dabbfaeec2b2163e8'}
OLD_WARNING = 'warning: MicroCFTA/InternedFreshOrdinaryClosedCompletion.lean:24:5: Variable name `inputs` is not explicitly referenced.'


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
    assert sources['counts'] == {'new_lean_jobs': 0, 'new_proof_pairs': 0,
                                 'reused_public_pairs': 4, 'owner_producers_proved': 0}
    for item in sources['sources']:
        snapshot = HERE / item['snapshot']
        assert snapshot.stat().st_size == item['bytes'] and sha(snapshot) == item['sha256']
        if args.live_root:
            assert sha(args.root / item['path']) == item['sha256'], item['path']
    for item in sources['candidates']:
        candidate = HERE / item['path']
        assert sha(candidate) == item['sha256'] == EXPECTED[candidate.name]
        assert candidate.read_bytes() == (HERE / 'inputs' / candidate.name).read_bytes()

    def receipt(stem):
        meta = read(HERE / 'receipts' / (stem + '.json'))
        assert meta['exit_code'] == 0
        assert meta['command'][0] in {
            '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean',
            '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake'}
        assert meta['wrapper'][meta['wrapper'].index('--mem') + 1] == '4G'
        assert meta['wrapper'][meta['wrapper'].index('--time') + 1] == '5m'
        assert read(HERE / 'receipts' / meta['limits']) == {
            'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
        if 'source' in meta:
            assert '-Dlinter.all=true' in meta['command']
            assert sha(HERE / 'receipts' / meta['source']) == meta['sha256']
        usage = HERE / 'receipts' / (stem + '.usage.json')
        if usage.exists():
            actual = read(usage)
            assert actual['age_seconds'] < 120 and actual['remaining_percent'] > 1
        return meta, (HERE / 'receipts' / meta['log']).read_text()

    selected = read(HERE / 'selection.json')
    assert selected['new_lean_jobs'] == selected['new_proof_pairs'] == 0
    assert selected['reused_public_pairs'] == 4 and len(selected['groups']) == 2
    for group in selected['groups']:
        candidate = HERE / group['candidate']
        direct, log = receipt(group['strict'])
        assert not log and (HERE / 'receipts' / direct['source']).read_bytes() == candidate.read_bytes()
        meta, log = receipt(group['stem'])
        source = HERE / 'receipts' / meta['source']
        text = source.read_text()
        if group['mode'] == 'import':
            assert text.splitlines()[0] == 'import MicroCFTA.' + candidate.stem
        else:
            assert source.read_bytes().startswith(candidate.read_bytes())
        for option in OPTIONS:
            assert 'set_option ' + option in text
        heads = group['heads']
        assert re.findall(r'^#check @([^\s]+)', text, re.M) == heads
        assert re.findall(r'^#print (?!axioms )([^\s]+)', text, re.M) == heads
        assert re.findall(r'^#print axioms ([^\s]+)', text, re.M) == heads
        for head in heads:
            assert re.search(r'(?:def|theorem) ' + re.escape(head) + r'(?:\.\{[^}]*\})?\s*:', log), head
        assert ':=' in log
        assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|maximum recursion depth|⋯|…|\.\.\.', log)
        reports = list(re.finditer(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", log))
        assert [match.group(1) for match in reports] == heads
        for match in reports:
            if match.group(2) is not None:
                axioms = re.sub(r'\.\{[^}]*\}', '', match.group(2))
                assert set(re.split(r',\s*', axioms.strip())) <= {'propext', 'Classical.choice', 'Quot.sound'}
    canonical, log = receipt(selected['canonical'])
    assert 'MicroCFTA.SourceCurrentNativeOptionalOwnerReceipt' in canonical['command']
    assert 'Build completed successfully' in log
    assert re.findall(r'^warning:.*$', log, re.M) == [OLD_WARNING]
    assert not re.search(r'(^|\n)error:', log)
    print(json.dumps({'status': 'PASS', 'live_root': args.live_root,
        'manifest_files': len(manifest['files']), 'root_foundations': len(sources['sources']),
        'reused_checked_public_pairs': 4, 'new_lean_jobs': 0, 'new_proof_pairs': 0,
        'owner_producers_proved': 0}))


if __name__ == '__main__':
    main()
