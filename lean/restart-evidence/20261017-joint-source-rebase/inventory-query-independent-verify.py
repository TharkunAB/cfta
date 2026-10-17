from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
MANIFEST = HERE / 'inventory-query-independent-manifest.json'


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

pairs(HERE / 'inventory-query-independent-public.lean', HERE / 'inventory-query-independent-public-1.log', 5)
pairs(HERE / 'inventory-query-independent-kernels.lean', HERE / 'inventory-query-independent-kernels-4.log', 2)
for stem, attempt in (('public', 1), ('kernels', 4)):
    assert sha(HERE / f'inventory-query-independent-{stem}.lean') == sha(
        HERE / f'inventory-query-independent-{stem}-{attempt}.source.lean')
for name, expected in (
    ('SourceCurrentConstrainedCapCheckedJointInventoryQuery', 'b2d3c1a093ffa6095ab0412ac83ed83aa8a2d37141fdb6c59da6ad44219e8e83'),
    ('SourceCurrentConstrainedCapCheckedJointInventoryCold', 'd1c7b7216346e20e60930f6ac32128dd1d5e21ef37b34bcc67baa4547f6d6400'),
):
    assert sha(ROOT / 'lean/MicroCFTA' / f'{name}.lean') == expected, name
for name, jobs in (('canonical-inventory-query-1.log', 1318), ('canonical-inventory-cold-joint-1.log', 1319)):
    assert f'Build completed successfully ({jobs} jobs).' in (HERE / name).read_text(), name
print('PASS: final Query/Cold sources; public5 + result-fed kernel2 full signature/axiom pairs; standard axioms; canonical1318/1319.')
