from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
MANIFEST = HERE / 'checked-edge-joint-manifest.json'

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def pairs(source, log, expected):
    text = source.read_text()
    for setting in ('linter.all true', 'pp.explicit true', 'pp.proofs true', 'pp.universes true',
                    'pp.deepTerms true', 'pp.fullNames true'):
        assert f'set_option {setting}' in text, (source, setting)
    assert re.search(r'set_option pp.maxSteps (\d+)', text)
    assert int(re.search(r'set_option pp.maxSteps (\d+)', text).group(1)) >= 1000000
    names = re.findall(r'^#print axioms (\S+)', text, re.M)
    checks = re.findall(r'^#check @(\S+)', text, re.M)
    assert len(names) == expected and names == checks, (source, names, checks)
    namespace = re.search(r'^namespace (\S+)', text, re.M)
    names = [name if '.' in name else namespace.group(1) + '.' + name for name in names]
    output = log.read_text()
    assert not re.search(r'error:|warning:|sorryAx', output), log
    for name in names:
        assert re.search(r"'" + re.escape(name) + r"' (?:depends on axioms:|does not depend on any axioms)", output), name
        assert re.search(r'^@?' + re.escape(name) + r'(?:\.\{[^}]+\})?\s*:', output, re.M), name
    for axioms in re.findall(r'depends on axioms: \[(.*?)\]', output, re.S):
        plain = re.sub(r'\.\{[^}]+\}', '', axioms)
        assert set(re.findall(r'[A-Za-z][A-Za-z.]*', plain)) <= {'propext', 'Classical.choice', 'Quot.sound'}, plain
    return expected

if MANIFEST.exists():
    for item in json.loads(MANIFEST.read_text())['files']:
        path = ROOT / item['path']
        assert path.stat().st_size == item['bytes'] and sha(path) == item['sha256'], item['path']
pairs(HERE / 'checked-edge-joint-public.lean', HERE / 'checked-edge-joint-public-1.log', 6)
pairs(HERE / 'checked-edge-joint-kernels.lean', HERE / 'checked-edge-joint-kernels-7.log', 3)
source = ROOT / 'lean/MicroCFTA/SourceCurrentConstrainedCapCheckedJointEdge.lean'
assert sha(source) == '1b3ef70b866b607d77789944ea9a607ae3198785702a2f1857664a2b03f26fff'
assert sha(source) == sha(HERE / 'checked-edge-joint-direct-3.source.lean')
assert sha(HERE / 'checked-edge-joint-public.lean') == sha(HERE / 'checked-edge-joint-public-1.source.lean')
assert sha(HERE / 'checked-edge-joint-kernels.lean') == sha(HERE / 'checked-edge-joint-kernels-7.source.lean')
assert (HERE / 'checked-edge-joint-direct-3.log').stat().st_size == 0
assert 'Build completed successfully (1184 jobs).' in (HERE / 'canonical-checked-joint-edge-1.log').read_text()
print('PASS: exact checked-edge source/snapshots; strict empty; six public and three constructive checked branch pairs; standard axioms; canonical1184.')
