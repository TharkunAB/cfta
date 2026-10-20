import argparse
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
BASE = 'mcfta-native-mu-optional-generation-math-review'


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, default=Path('/home/tritlo/Code/mcfta'))
    args = parser.parse_args()
    pins = json.loads((HERE / (BASE + '-source-pins.json')).read_text())
    for item in pins['files']:
        base = HERE if item['base'] == 'HERE' else args.root
        relative = Path(item['path'])
        assert not relative.is_absolute() and '..' not in relative.parts
        data = (base / relative).read_bytes()
        assert len(data) == item['bytes'] and hashlib.sha256(data).hexdigest() == item['sha256'], item['path']
    root = args.root
    folder = root / 'lean/restart-evidence/20261020-native-mu-generation'
    source = (root / 'lean/MicroCFTA/SourceCurrentNativeMuOptionalGeneration.lean').read_bytes()
    assert hashlib.sha256(source).hexdigest() == '128066eb8303114ea7653f7257707c5c4a5e3c5628213599f19703cd09491b80'
    assert source == (HERE / (BASE + '-reviewed-source.lean.txt')).read_bytes()
    assert source == (folder / 'generation-official-direct-3.source.lean').read_bytes()
    assert not (folder / 'generation-official-direct-3.log').read_bytes()
    for stem in ['generation-official-direct-3', 'generation-official-public-1', 'generation-official-canonical-1']:
        meta = json.loads((folder / (stem + '.json')).read_text())
        assert meta['exit_code'] == 0
        assert meta['wrapper'][meta['wrapper'].index('--mem') + 1] == '4G'
        assert meta['wrapper'][meta['wrapper'].index('--time') + 1] == '5m'
        assert json.loads((folder / (stem + '.limits.json')).read_text()) == {
            'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
        if 'sha256' in meta:
            assert hashlib.sha256((folder / meta['source']).read_bytes()).hexdigest() == meta['sha256']
    printer = (folder / 'generation-official-public-1.source.lean').read_text()
    assert printer.encode().startswith(source)
    for option in ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
                   'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']:
        assert 'set_option ' + option in printer
    for pattern in [r'^#check @', r'^#print (?!axioms )', r'^#print axioms ']:
        assert len(re.findall(pattern, printer, re.M)) == 2
    for suffix in ['maybeMu', 'trace']:
        name = 'MicroCFTA.SourceCurrentNativeMuOptionalGeneration.' + suffix
        for command in ['#check @', '#print ', '#print axioms ']:
            assert command + name in printer
    log = (folder / 'generation-official-public-1.log').read_text()
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    axioms = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
    assert len(axioms) == 2
    for item in axioms:
        names = re.sub(r'\.\{[^}]*\}', '', item)
        assert set(re.split(r',\s*', names.strip())) <= {'propext', 'Classical.choice', 'Quot.sound'}
    canonical = (folder / 'generation-official-canonical-1.log').read_text()
    assert len(re.findall(r'^warning:', canonical, re.M)) == 1
    assert 'MicroCFTA/InternedFreshOrdinaryClosedCompletion.lean:24:5:' in canonical
    assert not re.search(r'\berror:', canonical)
    assert pins['counts'] == {'new_lean_jobs': 0, 'new_proof_pairs': 0, 'reused_public_pairs': 2}
    print(json.dumps({'status': 'PASS', 'pins': len(pins['files']), 'new_lean_jobs': 0,
                      'new_proof_pairs': 0, 'reused_public_pairs': 2,
                      'canonical_warning': 'pre-existing ClosedCompletion:24:5'}))


if __name__ == '__main__':
    main()
