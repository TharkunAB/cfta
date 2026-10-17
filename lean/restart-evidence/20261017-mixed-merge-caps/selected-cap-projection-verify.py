from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
MANIFEST = HERE / 'selected-cap-projection-manifest.json'

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
pairs(HERE / 'selected-cap-projection-public.lean', HERE / 'selected-cap-projection-public-1.log', 5)
pairs(HERE / 'selected-cap-projection-kernels.lean', HERE / 'selected-cap-projection-kernels-3.log', 2)
source = ROOT / 'lean/MicroCFTA/SourceCurrentConstrainedCapSelectedProjection.lean'
assert sha(source) == 'ded575e227e5bf6d2fe822283a17657a366af4c95dfa67f4094f103d50a62d84'
assert sha(source) == sha(HERE / 'selected-cap-projection-direct-1.source.lean')
for kind, attempt in [('public', 1), ('kernels', 3)]:
    assert sha(HERE / f'selected-cap-projection-{kind}.lean') == sha(HERE / f'selected-cap-projection-{kind}-{attempt}.source.lean')
assert (HERE / 'selected-cap-projection-direct-1.log').stat().st_size == 0
assert 'Build completed successfully (1089 jobs).' in (HERE / 'canonical-selected-projection-1.log').read_text()
print('PASS: exact SelectedProjection; strict empty; public5 + own open-forest/negative-index kernel2 pairs; canonical1089.')
