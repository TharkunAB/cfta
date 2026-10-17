from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
MANIFEST = HERE / 'guard-normalization-independent-manifest.json'

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
pairs(HERE / 'guard-normalization-independent-public.lean', HERE / 'guard-normalization-independent-public-2.log', 18)
assert sha(HERE / 'guard-normalization-independent-public.lean') == sha(HERE / 'guard-normalization-independent-public-2.source.lean')
assert sha(ROOT / 'lean/MicroCFTA/SourceCurrentConstrainedCapGuardNormalization.lean') == '23a8af9ec1daefafe9b6f8e148430a2eb78e8c78b568130b7114fec9efab5210'
assert sha(ROOT / 'lean/MicroCFTA/SourceCurrentConstrainedCapGuardReadback.lean') == '285351c9938850e59f5d26951068169ff37b889ccf7e8781f731efeba30822db'
assert 'Build completed successfully (1004 jobs).' in (HERE / 'canonical-normalization-final.log').read_text()
assert 'Build completed successfully (1005 jobs).' in (HERE / 'canonical-readback-1.log').read_text()
print('PASS: final normalization/readback hashes, 18 independent public pairs, full signatures, standard axioms, canonical1004/1005.')
