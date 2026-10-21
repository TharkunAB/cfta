import argparse
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCE = 'SourceCurrentRequiredPositivePosition.lean'
HEADS = ['MicroCFTA.SourceCurrentRequiredPositivePosition.' + h for h in ['PositiveAt', 'not_plain', 'origin', 'required']]


def check(base, entry):
    data = (base / entry['path']).read_bytes()
    assert len(data) == entry['bytes'] and hashlib.sha256(data).hexdigest() == entry['sha256'], entry['path']


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, default=Path('/home/tritlo/Code/mcfta'))
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    manifest = json.loads((HERE / 'required-positive-manifest.json').read_text())
    for entry in manifest['files']:
        check(HERE, entry)
    for entry in manifest['sources']:
        check(HERE / 'inputs/root', entry)
        if args.live:
            check(args.root, entry)
    assert json.loads((HERE / 'required-positive-source-pins.json').read_text())['files'] == manifest['sources']
    selection = json.loads((HERE / 'required-positive-selection.json').read_text())
    assert selection['finalized'] and selection['public_heads'] == HEADS
    assert selection['lean_jobs'] == 3 and selection['failed_checks'] == 1
    assert selection['canonical_jobs'] == 0 and selection['constructed_pairs'] == 0
    source = (HERE / SOURCE).read_text()
    assert hashlib.sha256(source.encode()).hexdigest() == selection['source_sha256']
    assert source == (HERE / 'required-positive-direct-2.source.lean').read_text()
    assert len(source.splitlines()) == 97
    assert not re.search(r'\bsorry\b|\badmit\b|native_decide|trustCompiler', source)
    assert 'SourceEqualityProjectionLanguage.all₂_selected children childIndex child chosen' in source
    assert 'SourceEqualityRequiredWorkerSound.require_graph fuel readFuel needed original before result after actual' in source
    assert source.count('theorem required ') == 1 and source.count('SourceCurrentRequiredRowOrigins.node') == 1
    assert 'theorem origin {original result path}' in source
    assert '(actual : SourceEqualityRequiredWorker.require fuel readFuel needed original before = .done result after)' in source
    for name, code in selection['attempts'].items():
        meta = json.loads((HERE / (name + '.json')).read_text())
        assert meta['exit_code'] == code
        frozen = (HERE / meta['source']).read_bytes()
        assert hashlib.sha256(frozen).hexdigest() == meta['sha256']
        assert meta['wrapper'][meta['wrapper'].index('--mem') + 1] == '4G'
        assert meta['wrapper'][meta['wrapper'].index('--time') + 1] == '5m'
        assert json.loads((HERE / meta['limits']).read_text()) == {
            'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
        usage = json.loads((HERE / (name + '.usage.json')).read_text())
        assert usage['age_seconds'] < 120 and usage['remaining_percent'] > 1
        assert '-Dlinter.all=true' in meta['command']
        assert meta['command'][0].endswith('leanprover--lean4---v4.34.1/bin/lean')
    assert not (HERE / 'required-positive-direct-2.log').read_bytes()
    failed = (HERE / 'required-positive-direct-1.log').read_text()
    assert 'Invalid field `not_plain`' in failed and 'SourceCurrentRequiredExposureSafe.ExposureSafe' in failed
    printer = (HERE / 'required-positive-public-1.source.lean').read_text()
    assert printer.startswith(source)
    for option in ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
                   'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']:
        assert 'set_option ' + option in printer
    for h in HEADS:
        for directive in ['#check @', '#print ', '#print axioms ']:
            assert printer.count(directive + h + '\n') == 1
    log = (HERE / 'required-positive-public-1.log').read_text()
    assert len(log.encode()) == selection['public_log_bytes']
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    for index, h in enumerate(HEADS):
        report = re.search(re.escape("'" + h + "'") + r' depends on axioms:\s*\[([^\]]*)\]', log)
        assert report, h
        names = set(re.split(r',\s*', re.sub(r'\.\{[^}]*\}', '', report.group(1)).strip()))
        assert names <= {'propext', 'Classical.choice', 'Quot.sound'}, names
        if index:
            body = log.split('theorem ' + h, 1)[1].split("'" + h + "'", 1)[0]
            typ, proof = body.split(':=', 1)
            assert typ.strip() and proof.strip() and '_private' not in typ
    print(json.dumps({'status': 'PASS', 'pins': len(manifest['files']) + len(manifest['sources']),
                      'public_heads': 4, 'public_theorems': 3, 'constructed_pairs': 0,
                      'lean_jobs': 3, 'failed_checks': 1, 'canonical_jobs': 0, 'live': args.live}))


if __name__ == '__main__':
    main()
