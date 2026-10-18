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
    manifest = json.loads((HERE / 'publication-survival-kernels-manifest.json').read_text())
    for item in manifest['entries']:
        path = ROOT / item['path']
        assert path.is_file(), path
        assert path.stat().st_size == item['bytes'], path
        assert sha(path) == item['sha256'], path
    for stem in manifest['selected_executions']:
        meta = json.loads((HERE / (stem + '.json')).read_text())
        assert meta['exit_code'] == 0, stem
        assert meta['wrapper'][:5] == [
            '/home/tritlo/Code/heavy-management/bin/capped',
            '--mem', '4G', '--time', '5m',
        ], stem
        assert json.loads((HERE / meta['limits']).read_text()) == {
            'memory.max': '4294967296', 'memory.high': '4294967296',
            'memory.swap.max': '0',
        }, stem
        if 'source' in meta:
            frozen = HERE / meta['source']
            assert sha(frozen) == meta['sha256'], stem
            assert meta['command'] == [
                '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean',
                '-Dlinter.all=true', str(frozen),
            ], stem
        else:
            assert meta['command'][0] == '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake', stem
    for module in manifest['production']:
        live = ROOT / module['path']
        strict = json.loads((HERE / (module['strict'] + '.json')).read_text())
        assert sha(live) == module['sha256'] == sha(HERE / strict['source'])
        assert (HERE / strict['log']).stat().st_size == 0
    for stem in manifest['constructed_strict']:
        meta = json.loads((HERE / (stem + '.json')).read_text())
        assert (HERE / meta['log']).stat().st_size == 0
    for stem in manifest['canonical']:
        meta = json.loads((HERE / (stem + '.json')).read_text())
        assert re.search(r'Build completed successfully \(\d+ jobs\)\.', (HERE / meta['log']).read_text())
    for group in manifest['selected_groups'] + manifest.get('dependency_groups', []):
        meta = json.loads((HERE / (group['name'] + '.json')).read_text())
        source = (HERE / meta['source']).read_text()
        output = (HERE / meta['log']).read_text()
        for option in OPTIONS:
            assert 'set_option ' + option in source
        names = re.findall(r'^#check @([^\s]+)', source, re.M)
        assert len(names) == len(set(names)) == group['pairs']
        assert re.findall(r'^#print (?!axioms )([^\s]+)', source, re.M) == names
        assert re.findall(r'^#print axioms ([^\s]+)', source, re.M) == names
        assert not re.search(
            r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|'
            r'pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.',
            output,
        )
        reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', output)
        assert len(reports) + len(re.findall('does not depend on any axioms', output)) == group['pairs']
        for report in reports:
            cleaned = re.sub(r'\.\{[^}]*\}', '', report)
            assert set(re.split(r',\s*', cleaned.strip())) <= {
                'propext', 'Classical.choice', 'Quot.sound',
            }
    print(json.dumps({
        'status': 'PASS', 'entries': len(manifest['entries']),
        'owned_public_pairs': 0, 'constructed_pairs': 1,
        'strict_modules': 0,
    }, sort_keys=True))


if __name__ == '__main__':
    main()
