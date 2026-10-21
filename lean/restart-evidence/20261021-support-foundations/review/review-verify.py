import argparse
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent


def sha(path):
    with path.open('rb') as source:
        return hashlib.file_digest(source, 'sha256').hexdigest()


def check(base, item):
    path = base / item['path']
    assert path.stat().st_size == item['bytes'] and sha(path) == item['sha256'], str(path)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, default=Path('/home/tritlo/Code/mcfta'))
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    manifest = json.loads((HERE / 'review-manifest.json').read_text())
    for item in manifest['files']:
        check(HERE, item)
    pins = json.loads((HERE / 'source-pins.json').read_text())
    for item in pins['files']:
        check(HERE / 'inputs/root', item)
        if args.live:
            check(args.root, item)
    expected_axioms = [set(), {'propext', 'Quot.sound'}, {'propext', 'Quot.sound'}]
    for module in pins['candidates']:
        base = HERE / 'inputs' / module['label']
        source = HERE / module['source']
        assert sha(source) == module['sha256']
        for stem in [module['strict'], module['public']]:
            metadata = json.loads((base / (stem + '.json')).read_text())
            assert metadata['exit_code'] == 0
            assert sha(base / metadata['source']) == metadata['sha256']
            assert metadata['command'][0].endswith('leanprover--lean4---v4.34.1/bin/lean')
            assert '-Dlinter.all=true' in metadata['command']
            assert json.loads((base / metadata['limits']).read_text()) == {
                'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
        assert (base / (module['strict'] + '.log')).stat().st_size == 0
        assert (base / (module['strict'] + '.source.lean')).read_bytes() == source.read_bytes()
        printer = (base / (module['public'] + '.source.lean')).read_text()
        assert printer.startswith(source.read_text())
        for option in ['pp.explicit true', 'pp.fullNames true', 'pp.proofs true', 'pp.proofs.threshold 254',
                       'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000', 'linter.all true']:
            assert 'set_option ' + option in printer
        log = (base / (module['public'] + '.log')).read_text()
        assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
        actual = []
        for report in re.finditer(r'does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\]', log):
            actual.append(set() if report[1] is None else {
                part.strip() for part in re.sub(r'\.\{[^}]*\}', '', report[1]).split(',')})
        if module['label'] == 'child':
            assert len(log.encode()) == 79133
            assert actual == expected_axioms
            assert source.read_text().count('congruenceStep classes = some classes') == 5
        else:
            assert len(log.encode()) == 16252
            assert actual == [set()] + expected_axioms
            assert 'No semantic or physical storage premise is needed.' in source.read_text()
    print(json.dumps({'status': 'PASS', 'pins': len(manifest['files']), 'live': args.live,
                      'review_lean_jobs': 0, 'owned_public_pairs': 0, 'reused_public_pairs': 7,
                      'reused_strict_checks': 2, 'reused_full_checks': 2}))


if __name__ == '__main__':
    main()
