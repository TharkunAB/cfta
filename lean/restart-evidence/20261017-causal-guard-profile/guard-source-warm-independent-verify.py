from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
MANIFEST = HERE / 'guard-source-warm-independent-manifest.json'

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
pairs(HERE / 'guard-source-warm-independent-public.lean', HERE / 'guard-source-warm-independent-public-1.log', 6)
pairs(HERE / 'guard-source-warm-independent-kernels.lean', HERE / 'guard-source-warm-independent-kernels-3.log', 1)
assert sha(HERE / 'guard-source-warm-independent-public.lean') == sha(HERE / 'guard-source-warm-independent-public-1.source.lean')
assert sha(HERE / 'guard-source-warm-independent-kernels.lean') == sha(HERE / 'guard-source-warm-independent-kernels-3.source.lean')
assert sha(ROOT / 'lean/MicroCFTA/SourceCurrentConstrainedCapGuardExecution.lean') == '4cc5caf9414e0a777d1f4fc92ec79b467a83dff0516a0aeeb966a3f52bceb44e'
assert 'Build completed successfully (1010 jobs).' in (HERE / 'canonical-execution-1.log').read_text()
print('PASS: final actual producer hash, six independent public pairs, one constructive source-to-warm pair, full signatures, standard axioms, canonical1010.')
