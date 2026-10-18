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
    observed = json.loads((HERE / (stem + '.limits.json')).read_text())
    assert observed == {
        'memory.max': '4294967296', 'memory.high': '4294967296',
        'memory.swap.max': '0',
    }, (stem, observed)


def group(selected):
    stem, count = selected['name'], selected['pairs']
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert meta['exit_code'] == 0, stem
    source = (HERE / meta['source']).read_text()
    log = (HERE / meta['log']).read_text()
    for option in OPTIONS:
        assert 'set_option ' + option in source, (stem, option)
    names = re.findall(r'^#check @([^\s]+)', source, re.M)
    assert len(names) == len(set(names)) == count, stem
    assert re.findall(r'^#print (?!axioms )([^\s]+)', source, re.M) == names, stem
    assert re.findall(r'^#print axioms ([^\s]+)', source, re.M) == names, stem
    assert not re.search(
        r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|'
        r'pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.',
        log,
    ), stem
    reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
    assert len(reports) + len(re.findall(r'does not depend on any axioms', log)) == count, stem
    for report in reports:
        cleaned = re.sub(r'\.\{[^}]*\}', '', report)
        assert set(re.split(r',\s*', cleaned.strip())) <= {
            'propext', 'Classical.choice', 'Quot.sound',
        }, (stem, report)
    if selected['kind'] == 'new-public':
        headers = json.loads((HERE / 'class-origin-kernels-public-heads.json').read_text())
        expected = ['MicroCFTA.SourceCurrentActualClassRowOrigins.' + name for name in headers]
        assert names == expected
    limits(stem)


def main():
    manifest = json.loads((HERE / 'class-origin-kernels-manifest.json').read_text())
    for entry in manifest['entries']:
        path = ROOT / entry['path']
        assert path.is_file(), path
        assert path.stat().st_size == entry['bytes'], path
        assert sha(path) == entry['sha256'], path
    for attempt in manifest['attempts']:
        stem = attempt['name']
        meta = json.loads((HERE / (stem + '.json')).read_text())
        assert meta['exit_code'] == attempt['exit_code'], stem
        assert (HERE / meta['log']).is_file(), stem
        assert meta['wrapper'][0] == '/home/tritlo/Code/heavy-management/bin/capped', stem
        assert meta['wrapper'][1:5] == ['--mem', '4G', '--time', '5m'], stem
        if 'source' in meta:
            frozen = HERE / meta['source']
            assert sha(frozen) == meta['sha256'], stem
            assert meta['command'] == [
                '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean',
                '-Dlinter.all=true', str(frozen),
            ], stem
        else:
            assert meta['command'][:4] == [
                '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake',
                '-d', str(ROOT / 'lean'), 'build',
            ], stem
        limits(stem)
    for module, item in manifest['production'].items():
        live = ROOT / item['path']
        meta = json.loads((HERE / (item['strict'] + '.json')).read_text())
        assert meta['exit_code'] == 0 and not (HERE / meta['log']).read_bytes(), module
        assert sha(live) == item['sha256'] == sha(HERE / meta['source']), module
        limits(item['strict'])
    for stem in manifest['selected_canonical']:
        meta = json.loads((HERE / (stem + '.json')).read_text())
        assert meta['exit_code'] == 0, stem
        log = (HERE / meta['log']).read_text()
        assert re.search(r'Build completed successfully \(\d+ jobs\)\.', log), stem
        warnings = re.findall(r'^warning: ([^\n]+)', log, re.M)
        expected = ['MicroCFTA/InternedFreshOrdinaryClosedCompletion.lean:24:5:']
        assert len(warnings) == len(expected), (stem, warnings)
        assert all(warning.startswith(prefix) for warning, prefix in zip(warnings, expected)), stem
        assert not re.search(r'\berror(?:\([^)]*\))?:|failed to pretty print', log), stem
        limits(stem)
    kernel = json.loads((HERE / 'class-origin-kernels-4.json').read_text())
    assert kernel['exit_code'] == 0 and not (HERE / kernel['log']).read_bytes()
    for selected in manifest['selected_groups']:
        group(selected)
    group({'name': 'class-origin-public-1', 'pairs': 5, 'kind': 'reviewed-public'})
    strict_source = (HERE / kernel['source']).read_bytes()
    kernel_public = json.loads((HERE / 'class-origin-kernels-public-1.json').read_text())
    assert (HERE / kernel_public['source']).read_bytes().startswith(strict_source)
    print(json.dumps({
        'status': 'PASS', 'entries': len(manifest['entries']),
        'attempts': len(manifest['attempts']), 'reviewed_strict_modules': len(manifest['production']),
        'new_public_pairs': 0, 'reviewed_public_pairs': 5, 'constructed_pairs': 1, 'groups': 1,
        'effective_caps': '4GiB/4GiB/swap0',
        'infrastructure_failures_preserved': 0,
    }, sort_keys=True))


if __name__ == '__main__':
    main()
