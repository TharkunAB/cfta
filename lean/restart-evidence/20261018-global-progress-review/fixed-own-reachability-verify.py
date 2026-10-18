import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
OPTIONS = [
    'linter.all true', 'pp.explicit true', 'pp.fullNames true',
    'pp.proofs true', 'pp.proofs.threshold 254', 'pp.universes true',
    'pp.deepTerms true', 'pp.maxSteps 10000000',
]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    manifest = json.loads((HERE / 'fixed-own-reachability-manifest.json').read_text())
    for item in manifest['entries']:
        path = ROOT / item['path']
        assert path.is_file(), path
        assert path.stat().st_size == item['bytes'], path
        assert sha(path) == item['sha256'], path
    for item in manifest['executions']:
        stem = item['name']
        meta = json.loads((HERE / (stem + '.json')).read_text())
        assert meta['exit_code'] == item['exit_code'], stem
        source = HERE / meta['source']
        assert sha(source) == meta['sha256'], stem
        assert meta['command'] == [
            '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean',
            '-Dlinter.all=true', str(source),
        ]
        assert meta['wrapper'][:5] == [
            '/home/tritlo/Code/heavy-management/bin/capped',
            '--mem', '4G', '--time', '5m',
        ]
        assert json.loads((HERE / meta['limits']).read_text()) == {
            'memory.max': '4294967296', 'memory.high': '4294967296',
            'memory.swap.max': '0',
        }
        source_text = source.read_text()
        for option in OPTIONS:
            assert 'set_option ' + option in source_text
        log = (HERE / meta['log']).read_text()
        if item['kind'] == 'interrupted-proof-attempt':
            assert meta['exit_code'] == -15 and log == ''
        else:
            assert item['kind'] == 'executable-diagnostic' and meta['exit_code'] == 0
            assert log == ('MicroCFTA.EqualityNormalize.RunResult.normalized '
                           '[[[0], [1, 0, 0]], [[0, 1], [1, 0, 0, 1], [1, 0, 1]]]\n')
            assert '#eval ' in source_text and '#check' not in source_text
            assert not re.search(r'sorryAx|\b(?:error|warning)(?:\([^)]*\))?:|failed to pretty print', log)
    assert manifest['new_production_modules'] == 0
    assert manifest['verified_theorem_pairs'] == 0
    assert manifest['selected_groups'] == []
    print(json.dumps({
        'status': 'PASS', 'entries': len(manifest['entries']),
        'interrupted_proofs': 2, 'executable_diagnostics': 1,
        'new_production_modules': 0, 'verified_theorem_pairs': 0,
    }, sort_keys=True))


if __name__ == '__main__':
    main()
