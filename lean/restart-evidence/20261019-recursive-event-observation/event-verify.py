import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
OPTIONS = ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
           'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']
BAD = r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def meta(stem):
    data = json.loads((HERE / (stem + '.json')).read_text())
    assert data['wrapper'][1:5] == ['--mem', '4G', '--time', '5m'], stem
    assert 'leanprover--lean4---v4.34.1/bin/' in data['command'][0], stem
    limits = json.loads((HERE / data['limits']).read_text())
    assert limits == {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}, stem
    if 'source' in data:
        assert sha(HERE / data['source']) == data['sha256'], stem
    return data


def group(item):
    stem, count = item['name'], item['pairs']
    data = meta(stem)
    assert data['exit_code'] == 0, stem
    source = (HERE / data['source']).read_text()
    log = (HERE / data['log']).read_text()
    for option in OPTIONS:
        assert 'set_option ' + option in source, (stem, option)
    assert len(re.findall(r'^#check @', source, re.M)) == count, stem
    assert len(re.findall(r'^#print axioms ', source, re.M)) == count, stem
    assert len(re.findall(r'^#print (?!axioms )', source, re.M)) == count, stem
    assert not re.search(BAD, log), stem
    reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
    assert len(reports) + len(re.findall(r'does not depend on any axioms', log)) == count, stem
    for report in reports:
        cleaned = re.sub(r'\.\{[^}]*\}', '', report)
        assert set(re.split(r',\s*', cleaned.strip())) <= {'propext', 'Classical.choice', 'Quot.sound'}, stem


def main():
    manifest_path = HERE / 'event-manifest.json'
    manifest = json.loads(manifest_path.read_text())
    for item in manifest['files']:
        path = ROOT / item['path']
        assert path.stat().st_size == item['bytes'], item['path']
        assert sha(path) == item['sha256'], item['path']
    selection = json.loads((HERE / 'event-selection.json').read_text())
    assert selection['finalized']
    for stem in manifest['attempts']:
        meta(stem)
    for production, stem in selection['stricts'].items():
        strict = meta(stem)
        assert strict['exit_code'] == 0, stem
        assert (HERE / strict['log']).read_bytes() == b'', stem
        assert sha(ROOT / production) == selection['productions'][production], production
        assert sha(HERE / strict['source']) == selection['productions'][production], stem
    for stem in selection['canonicals']:
        canonical = meta(stem)
        assert canonical['exit_code'] == 0, stem
        log = (HERE / canonical['log']).read_text()
        assert len(re.findall(r'^warning:', log, re.M)) == 1, stem
        assert selection['canonical_allowed_warning_source'] in log, stem
        assert not re.search(r'\berror:', log), stem
        assert 'Build completed successfully' in log, stem
    for item in selection['groups']:
        group(item)
    assert len(manifest['attempts']) == selection['owned_lean_runs'] == 14
    assert sum(item['pairs'] for item in selection['groups']) == selection['public_pairs'] == 6
    assert selection['constructed_pairs'] == selection['auxiliary_pairs'] == 0
    print(json.dumps({'status': 'PASS', 'manifest_pins': len(manifest['files']),
                      'manifest_sha256': sha(manifest_path), 'public_pairs': 6,
                      'constructed_pairs': 0, 'auxiliary_pairs': 0,
                      'strict_zero_logs': 2, 'owned_lean_runs': 14,
                      'canonical': 'PASS with the unchanged dependency warning only'}, sort_keys=True))


if __name__ == '__main__':
    main()
