from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
MANIFEST = HERE / 'probe-binder-manifest.json'

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
pairs(HERE / 'probe-binder-public.lean', HERE / 'probe-binder-public-1.log', 16)
pairs(HERE / 'probe-binder-kernels.lean', HERE / 'probe-binder-kernels-3.log', 2)
assert sha(HERE / 'probe-binder-public.lean') == sha(HERE / 'probe-binder-public-1.source.lean')
assert sha(HERE / 'probe-binder-kernels.lean') == sha(HERE / 'probe-binder-kernels-3.source.lean')
for module, expected, snapshot, log in (
    ('NativeProbeSupport', '64f331b0d143dc2ee418d4e37b79d8b0da80a3cc6ccfd8a3ffdc71d0c957276f', 'probe-support-direct-1.source.lean', 'probe-support-direct-1.log'),
    ('NativeBinderReturn', '13901241fe72daae762af6dea471f9c74ba4cfbdd6b6ecda24af2d5a0edb6b80', 'binder-return-direct-3.source.lean', 'binder-return-direct-3.log')):
    source = ROOT / f'lean/MicroCFTA/SourceCurrentConstrainedCap{module}.lean'
    assert sha(source) == expected and sha(source) == sha(HERE / snapshot)
    assert (HERE / log).stat().st_size == 0
assert 'Build completed successfully (1139 jobs).' in (HERE / 'canonical-probe-support-1.log').read_text()
assert 'Build completed successfully (1172 jobs).' in (HERE / 'canonical-effects-binder-1.log').read_text()
print('PASS: two frozen production sources/snapshots; strict final logs empty; 16 public and two constructive kernel pairs; standard axioms; canonical1139/1172.')
