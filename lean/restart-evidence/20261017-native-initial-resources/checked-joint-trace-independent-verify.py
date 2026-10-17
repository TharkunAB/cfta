from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
MANIFEST = HERE / 'checked-joint-trace-independent-manifest.json'

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
pairs(HERE / 'checked-joint-trace-independent-public.lean', HERE / 'checked-joint-trace-independent-public-1.log', 4)
expected = {
    'SourceCurrentConstrainedCapCheckedJointInduction': 'e9e5515458284ccd303e740d4f1596af455d0f57bb4997e60caaf2149280d368',
    'SourceCurrentConstrainedCapCheckedJointTrace': '9cda211eeb18a7ae1e02c7c2b7e69a3b74aa7a2306660183baf8738013aa1d9d',
}
for name, digest in expected.items():
    assert sha(ROOT / 'lean/MicroCFTA' / (name + '.lean')) == digest
assert sha(HERE / 'checked-joint-trace-independent-public.lean') == sha(HERE / 'checked-joint-trace-independent-public-1.source.lean')
assert 'Build completed successfully (1232 jobs).' in (HERE / 'canonical-checked-joint-trace-1.log').read_text()
assert 'Build completed successfully (1246 jobs).' in (HERE / 'canonical-checked-joint-induction-compile-1.log').read_text()
print('PASS: exact Induction/Trace sources; four imported full-signature/axiom pairs; standard axioms; canonical1246/1232; independent review frozen.')
