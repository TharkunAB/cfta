import argparse
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
HEADS = ['MicroCFTA.SourceCurrentRequiredPositivePosition.' + name for name in
         ['PositiveAt', 'not_plain', 'origin', 'required']]


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
    base = HERE / 'inputs/candidate'
    source = HERE / pins['candidate']['path']
    assert sha(source) == pins['candidate']['sha256']
    text = source.read_text()
    assert len(text.splitlines()) == 97
    assert text.count('SourceCurrentRequiredRowOrigins.node') == 1
    assert text.count('SourceEqualityRequiredWorkerSound.require_graph') == 1
    assert 'SourceEqualityProjectionLanguage.all₂_selected children childIndex child chosen' in text
    assert 'SourceCurrentHereditaryUnconstrained.union_member' in text
    assert not re.search(r'\b(?:sorry|admit|axiom)\b', text)
    for stem in ['required-positive-direct-2', 'required-positive-public-1']:
        metadata = json.loads((base / (stem + '.json')).read_text())
        assert metadata['exit_code'] == 0
        assert sha(base / metadata['source']) == metadata['sha256']
        assert metadata['command'][0].endswith('leanprover--lean4---v4.34.1/bin/lean')
        assert '-Dlinter.all=true' in metadata['command']
        assert metadata['wrapper'][metadata['wrapper'].index('--mem') + 1] == '4G'
        assert metadata['wrapper'][metadata['wrapper'].index('--time') + 1] == '5m'
        assert json.loads((base / metadata['limits']).read_text()) == {
            'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
        usage = json.loads((base / (stem + '.usage.json')).read_text())
        assert usage['age_seconds'] < 120 and usage['remaining_percent'] > 1
    assert (base / 'required-positive-direct-2.log').stat().st_size == 0
    assert (base / 'required-positive-direct-2.source.lean').read_bytes() == source.read_bytes()
    printer = (base / 'required-positive-public-1.source.lean').read_text()
    assert printer.startswith(text)
    for option in ['pp.explicit true', 'pp.fullNames true', 'pp.proofs true', 'pp.proofs.threshold 254',
                   'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000', 'linter.all true']:
        assert 'set_option ' + option in printer
    for head in HEADS:
        for directive in ['#check @', '#print ', '#print axioms ']:
            assert printer.count(directive + head) == 1
    log = (base / 'required-positive-public-1.log').read_text()
    assert len(log.encode()) == 155756
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
    axioms = [{part.strip() for part in re.sub(r'\.\{[^}]*\}', '', report).split(',')} for report in reports]
    assert axioms == [{'propext', 'Classical.choice', 'Quot.sound'}] * 4
    print(json.dumps({'status': 'PASS', 'pins': len(manifest['files']), 'live': args.live,
                      'review_lean_jobs': 0, 'owned_public_pairs': 0, 'reused_public_pairs': 4,
                      'reused_strict_checks': 1, 'reused_full_checks': 1}))


if __name__ == '__main__':
    main()
