import argparse
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
HEADS = ['MicroCFTA.SourceCurrentNativeOriginalPublicationTrace.' + name
         for name in ['build_trace_warm_writers', 'build_trace_warm_target']]


def check(base, entry):
    data = (base / entry['path']).read_bytes()
    assert len(data) == entry['bytes'] and hashlib.sha256(data).hexdigest() == entry['sha256'], entry['path']


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, default=Path('/home/tritlo/Code/mcfta'))
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    manifest = json.loads((HERE / 'warm-publication-trace-manifest.json').read_text())
    for entry in manifest['files']:
        check(HERE, entry)
    for entry in manifest['sources']:
        check(HERE / 'inputs/root', entry)
        if args.live:
            check(args.root, entry)
    assert json.loads((HERE / 'warm-publication-trace-source-pins.json').read_text())['files'] == manifest['sources']
    source = (HERE / 'SourceCurrentNativeOriginalPublicationTrace.lean').read_text()
    old = (HERE / 'publication-trace-before.lean.txt').read_text()
    end = '\nend MicroCFTA.SourceCurrentNativeOriginalPublicationTrace\n'
    assert old.endswith(end) and source.startswith(old[:-len(end)]) and source.endswith(end)
    assert source.count('theorem build_trace_warm_writers ') == 1
    assert source.count('theorem build_trace_warm_target ') == 1
    assert source.count('build_trace_warm_writers original initial before context result after actual') == 1
    for text in ['before.nodeRecords key = some (.mu entry body depth ordinary) ∨',
                 'earlierIndex < index', 'Value.mu.inj valueSame', 'rw [missing] at prior']:
        assert text in source
    launch = json.loads((HERE / 'warm-publication-trace-direct-1.json').read_text())
    assert launch['exit_code'] == 1
    assert 'Failed to connect to bus: Operation not permitted' in (HERE / launch['log']).read_text()
    assert not (HERE / launch['limits']).exists()
    assert (HERE / launch['source']).read_text() == source
    for stem in ['warm-publication-trace-direct-2', 'warm-publication-trace-public-1']:
        meta = json.loads((HERE / (stem + '.json')).read_text())
        assert meta['exit_code'] == 0 and '-Dlinter.all=true' in meta['command']
        assert meta['command'][0] == '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean'
        assert hashlib.sha256((HERE / meta['source']).read_bytes()).hexdigest() == meta['sha256']
        assert json.loads((HERE / meta['limits']).read_text()) == {
            'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
        assert meta['wrapper'][meta['wrapper'].index('--mem') + 1] == '4G'
        assert meta['wrapper'][meta['wrapper'].index('--time') + 1] == '5m'
        usage = json.loads((HERE / (stem + '.usage.json')).read_text())
        assert usage['remaining_percent'] > 1 and usage['age_seconds'] < 120
    assert (HERE / 'warm-publication-trace-direct-2.source.lean').read_text() == source
    assert not (HERE / 'warm-publication-trace-direct-2.log').read_bytes()
    printer = (HERE / 'warm-publication-trace-public-1.source.lean').read_text()
    assert printer.startswith(source)
    for option in ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
                   'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']:
        assert 'set_option ' + option in printer
    log = (HERE / 'warm-publication-trace-public-1.log').read_text()
    assert len(log.encode()) == 2053670
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    for head in HEADS:
        for directive in ['#check @', '#print ', '#print axioms ']:
            assert printer.count(directive + head) == 1
        printed = log.split('theorem ' + head, 1)[1]
        printed_type, proof = printed.split(':=', 1)
        assert not any(name in printed_type for name in ['_private', 'Rooted', 'Supported', 'WrittenIn'])
        assert proof.strip()
    reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
    assert len(reports) == 2
    for report in reports:
        assert set(re.split(r',\s*', re.sub(r'\.\{[^}]*\}', '', report).strip())) == {'propext', 'Classical.choice', 'Quot.sound'}
    selection = json.loads((HERE / 'warm-publication-trace-selection.json').read_text())
    assert selection['finalized'] and selection['public_heads'] == HEADS
    assert selection['command_attempts'] == 3 and selection['lean_jobs'] == 2
    assert selection['failed_lean_checks'] == 0 and selection['failed_launches'] == 1
    print(json.dumps({'status': 'PASS', 'pins': len(manifest['files']) + len(manifest['sources']),
                      'new_public_pairs': 2, 'constructed_pairs': 0, 'lean_jobs': 2,
                      'command_attempts': 3, 'failed_launches': 1, 'canonical_jobs': 0, 'live': args.live}))


if __name__ == '__main__':
    main()
