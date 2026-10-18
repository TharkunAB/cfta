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
    limits(stem)


def main():
    manifest = json.loads((HERE / 'selected-progress-manifest.json').read_text())
    for entry in manifest['entries']:
        path = ROOT / entry['path']
        assert path.is_file() and path.stat().st_size == entry['bytes'], path
        assert sha(path) == entry['sha256'], path
    for attempt in manifest['attempts']:
        stem = attempt['name']
        meta = json.loads((HERE / (stem + '.json')).read_text())
        assert meta['exit_code'] == attempt['exit_code'], stem
        frozen = HERE / meta['source']
        assert sha(frozen) == meta['sha256'], stem
        assert meta['command'] == [
            '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean',
            '-Dlinter.all=true', str(frozen),
        ], stem
        assert meta['wrapper'][0] == '/home/tritlo/Code/heavy-management/bin/capped', stem
        assert meta['wrapper'][1:5] == ['--mem', '4G', '--time', '5m'], stem
        limits(stem)
    for module, item in manifest['production'].items():
        meta = json.loads((HERE / (item['strict'] + '.json')).read_text())
        assert meta['exit_code'] == 0 and not (HERE / meta['log']).read_bytes(), module
        assert sha(ROOT / item['path']) == item['sha256'] == sha(HERE / meta['source']), module
        limits(item['strict'])
    for stem in manifest['reviewed_canonical']:
        meta = json.loads((HERE / (stem + '.json')).read_text())
        assert meta['exit_code'] == 0, stem
        log = (HERE / meta['log']).read_text()
        assert re.search(r'Build completed successfully \(\d+ jobs\)\.', log), stem
        warnings = re.findall(r'^warning: ([^\n]+)', log, re.M)
        assert len(warnings) == 1 and warnings[0].startswith('MicroCFTA/InternedFreshOrdinaryClosedCompletion.lean:24:5:'), stem
        assert not re.search(r'\berror(?:\([^)]*\))?:|failed to pretty print', log), stem
        limits(stem)
    selected = json.loads((HERE / 'selected-progress-selection.json').read_text())
    assert selected['finalized']
    kernel = json.loads((HERE / (selected['constructed_strict'] + '.json')).read_text())
    assert kernel['exit_code'] == 0 and not (HERE / kernel['log']).read_bytes()
    strict_source = (HERE / kernel['source']).read_text()
    for item in selected['selected_groups']:
        group(item)
        meta = json.loads((HERE / (item['name'] + '.json')).read_text())
        public_source = (HERE / meta['source']).read_text()
        for option in OPTIONS[1:]:
            public_source = public_source.replace('set_option ' + option + '\n', '', 1)
        assert public_source.startswith(strict_source)
    for item in manifest['reviewed_public_not_selected']:
        group(item)
    print(json.dumps({'status':'PASS','entries':len(manifest['entries']),
        'attempts':len(manifest['attempts']),'reviewed_modules':len(manifest['production']),
        'new_public_pairs':0,'reviewed_public_pairs':7,'constructed_pairs':1,'groups':1,
        'effective_caps':'4GiB/4GiB/swap0'},sort_keys=True))


if __name__ == '__main__':
    main()
