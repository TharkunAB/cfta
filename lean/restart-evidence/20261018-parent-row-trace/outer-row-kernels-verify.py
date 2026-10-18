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


def limits(stem):
    actual = json.loads((HERE / (stem + '.limits.json')).read_text())
    assert actual == {
        'memory.max': '4294967296', 'memory.high': '4294967296',
        'memory.swap.max': '0',
    }, (stem, actual)


def main():
    manifest = json.loads((HERE / 'outer-row-kernels-manifest.json').read_text())
    for entry in manifest['entries']:
        path = ROOT / entry['path']
        assert path.is_file(), path
        assert path.stat().st_size == entry['bytes'], path
        assert sha(path) == entry['sha256'], path
    for attempt in manifest['attempts']:
        stem = attempt['name']
        meta = json.loads((HERE / (stem + '.json')).read_text())
        assert meta['exit_code'] == attempt['exit_code'], stem
        snapshot = HERE / meta['source']
        assert sha(snapshot) == meta['sha256'], stem
        assert meta['command'] == [
            '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean',
            '-Dlinter.all=true', str(snapshot),
        ], stem
        assert meta['wrapper'][:5] == [
            '/home/tritlo/Code/heavy-management/bin/capped',
            '--mem', '4G', '--time', '5m',
        ], stem
        assert Path(meta['wrapper'][-1]) == HERE / 'outer-row-kernels-capped-worker.py'
        assert (HERE / meta['log']).is_file(), stem
        limits(stem)
    module = manifest['dependency']
    source = ROOT / module['path']
    strict = json.loads((HERE / (module['strict'] + '.json')).read_text())
    assert strict['exit_code'] == 0
    assert sha(source) == module['sha256'] == sha(HERE / strict['source'])
    assert (HERE / strict['log']).stat().st_size == 0
    limits(module['strict'])
    canonical = json.loads((HERE / (module['canonical'] + '.json')).read_text())
    assert canonical['exit_code'] == 0
    canonical_log = (HERE / canonical['log']).read_text()
    assert re.search(r'Build completed successfully \(\d+ jobs\)\.', canonical_log)
    assert not re.search(r'\berror(?:\([^)]*\))?:|failed to pretty print', canonical_log)
    limits(module['canonical'])
    strict_name = manifest['selected_strict']
    strict = json.loads((HERE / (strict_name + '.json')).read_text())
    assert strict['exit_code'] == 0
    assert (HERE / strict['log']).stat().st_size == 0
    group = manifest['selected_groups'][0]
    meta = json.loads((HERE / (group['name'] + '.json')).read_text())
    assert meta['exit_code'] == 0
    text = (HERE / meta['source']).read_text()
    output = (HERE / meta['log']).read_text()
    assert text.startswith((HERE / strict['source']).read_text())
    for option in OPTIONS:
        assert 'set_option ' + option in text, option
    names = re.findall(r'^#check @([^\s]+)', text, re.M)
    assert names == group['declarations'] and len(names) == group['pairs'] == 1
    assert re.findall(r'^#print (?!axioms )([^\s]+)', text, re.M) == names
    assert re.findall(r'^#print axioms ([^\s]+)', text, re.M) == names
    assert not re.search(
        r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|'
        r'pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.',
        output,
    )
    reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', output)
    assert len(reports) == 1
    for report in reports:
        cleaned = re.sub(r'\.\{[^}]*\}', '', report)
        assert set(re.split(r',\s*', cleaned.strip())) <= {
            'propext', 'Classical.choice', 'Quot.sound',
        }, report
    print(json.dumps({
        'status': 'PASS', 'entries': len(manifest['entries']),
        'attempts': len(manifest['attempts']), 'constructed_pairs': 1,
        'strict_bytes': 0, 'limits': '4GiB/4GiB/swap0',
    }, sort_keys=True))


if __name__ == '__main__':
    main()
