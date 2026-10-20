import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = Path('/home/tritlo/Code/mcfta')
OPTIONS = [
    'linter.all true', 'pp.explicit true', 'pp.fullNames true',
    'pp.proofs true', 'pp.proofs.threshold 254', 'pp.universes true',
    'pp.deepTerms true', 'pp.maxSteps 10000000',
]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_limits(stem):
    path = HERE / (stem + '.limits.json')
    if path.exists():
        limits = json.loads(path.read_text())
        assert limits['memory.max'] == limits['memory.high'] == '4294967296', (stem, limits)
        assert limits['memory.swap.max'] == '0', (stem, limits)
    elif (HERE / (stem + '.caps')).exists():
        assert (HERE / (stem + '.caps')).read_text().split() == ['4294967296', '4294967296', '0'], stem
    else:
        log = (HERE / (stem + '.log')).read_text()
        assert log.splitlines()[:3] == ['4294967296', '4294967296', '0'], stem


def check_group(group):
    stem, count = group['name'], group['pairs']
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert meta['exit_code'] == 0, (stem, meta)
    source = (HERE / meta['source']).read_text()
    log = (HERE / meta['log']).read_text()
    for option in OPTIONS:
        assert 'set_option ' + option in source, (stem, option)
    assert len(re.findall(r'^#check @', source, re.M)) == count, stem
    assert len(re.findall(r'^#print axioms ', source, re.M)) == count, stem
    if group['full_proof']:
        assert len(re.findall(r'^#print (?!axioms )', source, re.M)) == count, stem
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log), stem
    reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
    assert len(reports) + len(re.findall(r'does not depend on any axioms', log)) == count, stem
    for report in reports:
        cleaned = re.sub(r'\.\{[^}]*\}', '', report)
        assert set(re.split(r',\s*', cleaned.strip())) <= {'propext', 'Classical.choice', 'Quot.sound'}, (stem, report)
    check_limits(stem)


if __name__ == '__main__':
    groups = json.loads((HERE / 'selected-groups.json').read_text())
    for group in groups:
        check_group(group)
    stricts = json.loads((HERE / 'selected-strict.json').read_text())
    for module, stem in stricts.items():
        meta = json.loads((HERE / (stem + '.json')).read_text())
        assert meta['exit_code'] == 0
        assert not (HERE / meta['log']).read_bytes(), stem
        assert sha(HERE / meta['source']) == sha(ROOT / 'lean/MicroCFTA' / (module + '.lean')), module
        check_limits(stem)
    selection = json.loads((HERE / 'selection-status.json').read_text())
    print(json.dumps({'status': 'PASS' if selection['finalized'] else 'PARTIAL', 'groups': len(groups),
        'public_pairs': sum(group['pairs'] for group in groups if group['kind'] == 'new-public'),
        'constructed_pairs': sum(group['pairs'] for group in groups if group['kind'] == 'constructed'),
        'strict_modules': len(stricts)}))
