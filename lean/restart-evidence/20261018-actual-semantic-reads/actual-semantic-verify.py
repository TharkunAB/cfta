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
    manifest = json.loads((HERE / 'actual-semantic-manifest.json').read_text())
    for entry in manifest['entries']:
        path = ROOT / entry['path']
        assert path.is_file() and path.stat().st_size == entry['bytes'], path
        assert sha(path) == entry['sha256'], path
    for module, item in manifest['production'].items():
        meta = json.loads((HERE / (item['strict'] + '.json')).read_text())
        assert meta['exit_code'] == 0 and not (HERE / meta['log']).read_bytes(), module
        assert sha(ROOT / item['path']) == item['sha256'] == sha(HERE / meta['source']), module
        limits(item['strict'])
        canonical = item['canonical']
        meta = json.loads((HERE / (canonical + '.json')).read_text())
        assert meta['exit_code'] == 0, canonical
        log = (HERE / meta['log']).read_text()
        assert re.search(r'Build completed successfully \(\d+ jobs\)\.', log), canonical
        warnings = re.findall(r'^warning: ([^\n]+)', log, re.M)
        assert len(warnings) == 1 and warnings[0].startswith('MicroCFTA/InternedFreshOrdinaryClosedCompletion.lean:24:5:'), canonical
        assert not re.search(r'\berror(?:\([^)]*\))?:|failed to pretty print', log), canonical
        limits(canonical)
    for stem in manifest['reviewed_constructed_strict']:
        meta = json.loads((HERE / (stem + '.json')).read_text())
        assert meta['exit_code'] == 0 and not (HERE / meta['log']).read_bytes(), stem
        assert sha(HERE / meta['source']) == meta['sha256'], stem
        limits(stem)
    for item in manifest['reviewed_groups_not_selected']:
        group(item)
    print(json.dumps({'status':'PASS','entries':len(manifest['entries']),
        'reviewed_modules':len(manifest['production']),
        'reviewed_public_pairs':sum(g['pairs'] for g in manifest['reviewed_groups_not_selected'] if g['kind']=='public'),
        'reviewed_constructed_pairs':sum(g['pairs'] for g in manifest['reviewed_groups_not_selected'] if g['kind']=='constructed'),
        'new_public_pairs':0,'new_constructed_pairs':0,'new_groups':0},sort_keys=True))


if __name__ == '__main__':
    main()
