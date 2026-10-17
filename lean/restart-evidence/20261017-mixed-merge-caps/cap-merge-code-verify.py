from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
MANIFEST = HERE / 'cap-merge-code-manifest.json'

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def pairs(source, log, expected):
    text = source.read_text()
    for setting in ('linter.all true', 'pp.explicit true', 'pp.proofs true', 'pp.universes true',
                    'pp.deepTerms true', 'pp.fullNames true'):
        assert f'set_option {setting}' in text, (source, setting)
    assert int(re.search(r'set_option pp.maxSteps (\d+)', text).group(1)) >= 1000000
    names = re.findall(r'^#print axioms (\S+)', text, re.M)
    checks = re.findall(r'^#check @(\S+)', text, re.M)
    assert len(names) == expected and names == checks, (source, names, checks)
    namespace = re.search(r'^namespace (\S+)', text, re.M)
    names = [name if '.' in name else namespace.group(1) + '.' + name for name in names]
    output = log.read_text()
    assert not re.search(r'\berror(?:\(|:)|\bwarning(?:\(|:)|sorryAx', output), log
    for name in names:
        assert re.search(r"'" + re.escape(name) + r"' (?:depends on axioms:|does not depend on any axioms)", output), name
        assert re.search(r'^@?' + re.escape(name) + r'(?:\.\{[^}]+\})?\s*:', output, re.M), name
    for axioms in re.findall(r'depends on axioms: \[(.*?)\]', output, re.S):
        plain = re.sub(r'\.\{[^}]+\}', '', axioms)
        assert set(re.findall(r'[A-Za-z][A-Za-z.]*', plain)) <= {'propext', 'Classical.choice', 'Quot.sound'}, plain


if MANIFEST.exists():
    for item in json.loads(MANIFEST.read_text())['files']:
        path = ROOT / item['path']
        assert path.stat().st_size == item['bytes'] and sha(path) == item['sha256'], item['path']
pairs(HERE / 'cap-merge-code-public.lean', HERE / 'cap-merge-code-public-1.log', 14)
pairs(HERE / 'cap-merge-code-kernels.lean', HERE / 'cap-merge-code-kernels-1.log', 3)
source = ROOT / 'lean/MicroCFTA/SourceCurrentConstrainedCapMemoMergeCode.lean'
assert sha(source) == 'd8d2474909ecad35dad4d9ed13b879446b40f7005332ed419244e4330743da04'
assert sha(source) == sha(HERE / 'cap-merge-code-direct-2.source.lean')
for kind in ('public', 'kernels'):
    assert sha(HERE / f'cap-merge-code-{kind}.lean') == sha(HERE / f'cap-merge-code-{kind}-1.source.lean')
assert (HERE / 'cap-merge-code-direct-2.log').stat().st_size == 0
assert 'Build completed successfully (1044 jobs).' in (HERE / 'canonical-cap-merge-code-1.log').read_text()
print('PASS: exact Code source; strict empty; public14 + constructive kernel3 signature/axiom pairs; canonical1044.')
