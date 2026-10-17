from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
MANIFEST = HERE / 'joint-execution-independent-manifest.json'

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
pairs(HERE / 'joint-execution-independent-public.lean', HERE / 'joint-execution-independent-public-1.log', 5)
pairs(HERE / 'joint-execution-independent-kernels.lean', HERE / 'joint-execution-independent-kernels-3.log', 1)
expected = {
    'SourceCurrentConstrainedCapKernelJointCalls': 'f51256dfea5b968b709bd61bda943584591cc24190808659c4086e6c1a9fbd1f',
    'SourceCurrentConstrainedCapKernelJointExecution': 'bad45c7705ca6282fa5becb5255b300828641d166ce2d711f2b35b4c52b9fe47',
}
for name, digest in expected.items():
    assert sha(ROOT / 'lean/MicroCFTA' / (name + '.lean')) == digest
assert sha(HERE / 'joint-execution-independent-public.lean') == sha(HERE / 'joint-execution-independent-public-1.source.lean')
assert sha(HERE / 'joint-execution-independent-kernels.lean') == sha(HERE / 'joint-execution-independent-kernels-3.source.lean')
assert sha(HERE / 'joint-execution-independent-kernels-2.source.lean') == sha(HERE / 'joint-execution-independent-kernels-3.source.lean')
assert 'Build completed successfully (2816 jobs).' in (HERE / 'lean-audit-final.log').read_text()
assert 'Checked axiom dependencies of 62897 MicroCFTA theorems.' in (HERE / 'lean-audit-final.log').read_text()
assert sha(HERE / 'kernel-joint-calls-direct-5.source.lean') == expected['SourceCurrentConstrainedCapKernelJointCalls']
assert sha(HERE / 'kernel-joint-execution-direct-2.source.lean') == expected['SourceCurrentConstrainedCapKernelJointExecution']
assert (HERE / 'kernel-joint-calls-direct-5.log').stat().st_size == 0
assert (HERE / 'kernel-joint-execution-direct-2.log').stat().st_size == 0
print('PASS: exact final Calls/Execution; all five public pairs and one constructive mixed recursive query pair; standard axioms; final Audit2816/62897.')
