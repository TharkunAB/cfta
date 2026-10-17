from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
MANIFEST = HERE / 'guard-depth-manifest.json'

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
    manifest = json.loads(MANIFEST.read_text())
    for item in manifest['files']:
        path = ROOT / item['path']
        assert path.stat().st_size == item['bytes'] and sha(path) == item['sha256'], item['path']
assert (HERE / 'guard-depth-direct-6.log').stat().st_size == 0
assert sha(ROOT / 'lean/MicroCFTA/SourceCurrentConstrainedCapGuardDepth.lean') == \
    '04442c331eedefe4329f0cd30192e7fd86f76901cb431ead92a4075c97ef2a6c'
assert sha(ROOT / 'lean/MicroCFTA/SourceCurrentConstrainedCapGuardDepth.lean') == sha(HERE / 'guard-depth-direct-6.source.lean')
assert sha(HERE / 'guard-depth-kernels.lean') == sha(HERE / 'guard-depth-kernels-6.source.lean')
assert sha(HERE / 'guard-depth-public.lean') == sha(HERE / 'guard-depth-public-1.source.lean')
pairs(HERE / 'guard-depth-public.lean', HERE / 'guard-depth-public-1.log', 28)
pairs(HERE / 'guard-depth-kernels.lean', HERE / 'guard-depth-kernels-6.log', 2)
assert 'Build completed successfully (1096 jobs).' in (HERE / 'canonical-components-1.log').read_text()
print('PASS: exact frozen production/snapshots; 28 public pairs; 2 constructive kernel pairs; standard axioms; canonical1096; strict final log empty.')
