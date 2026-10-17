from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
MANIFEST = HERE / 'stored-cap-manifest.json'

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
assert (HERE / 'stored-cap-direct-5.log').stat().st_size == 0
assert sha(ROOT / 'lean/MicroCFTA/SourceCurrentConstrainedCapStoredSubstitution.lean') == \
    '75a50564313d590e9f1c238929791aa49af824b681f050ed03a1bee63e18008b'
assert sha(ROOT / 'lean/MicroCFTA/SourceCurrentConstrainedCapStoredSubstitution.lean') == sha(HERE / 'stored-cap-direct-5.source.lean')
assert sha(HERE / 'stored-cap-kernels.lean') == sha(HERE / 'stored-cap-kernels-3.source.lean')
assert sha(HERE / 'stored-cap-public.lean') == sha(HERE / 'stored-cap-public-1.source.lean')
pairs(HERE / 'stored-cap-public.lean', HERE / 'stored-cap-public-1.log', 6)
pairs(HERE / 'stored-cap-kernels.lean', HERE / 'stored-cap-kernels-3.log', 1)
assert 'Build completed successfully (1086 jobs).' in (HERE / 'cap-stored-substitution-build.log').read_text()
print('PASS: exact frozen production/snapshots; 6 public pairs; 1 constructive kernel pair; standard axioms; canonical1086; strict final log empty.')
