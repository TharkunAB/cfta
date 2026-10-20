import argparse
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
HEADS = ['MicroCFTA.SourceCurrentNativeOriginalPublicationTrace.' + n for n in ['events', 'build_trace_writers']]
ATTEMPTS = {'publication-trace-direct-1': 1, 'publication-trace-direct-2': 1,
            'publication-trace-direct-3': 0, 'publication-trace-public-1': 0}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, default=Path('/home/tritlo/Code/mcfta'))
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    manifest = json.loads((HERE / 'publication-trace-manifest.json').read_text())
    for base, entries in [(HERE, manifest['files']), (args.root, manifest['sources'])]:
        for entry in entries:
            data = (base / entry['path']).read_bytes()
            assert len(data) == entry['bytes'], entry['path']
            assert hashlib.sha256(data).hexdigest() == entry['sha256'], entry['path']
    for stem, expected in ATTEMPTS.items():
        meta = json.loads((HERE / (stem + '.json')).read_text())
        assert meta['exit_code'] == expected and '-Dlinter.all=true' in meta['command']
        assert meta['command'][0] == '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean'
        assert hashlib.sha256((HERE / meta['source']).read_bytes()).hexdigest() == meta['sha256']
        assert json.loads((HERE / meta['limits']).read_text()) == {
            'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
        assert meta['wrapper'][0] == '/home/tritlo/Code/heavy-management/bin/capped'
        assert meta['wrapper'][meta['wrapper'].index('--mem') + 1] == '4G'
        assert meta['wrapper'][meta['wrapper'].index('--time') + 1] == '5m'
        usage = json.loads((HERE / (stem + '.usage.json')).read_text())
        assert usage['remaining_percent'] > 1 and usage['age_seconds'] < 120
    source = (HERE / 'SourceCurrentNativeOriginalPublicationTrace.lean').read_text()
    assert source == (HERE / 'publication-trace-direct-3.source.lean').read_text()
    assert not (HERE / 'publication-trace-direct-3.log').read_bytes()
    assert 'depthMember' in (HERE / 'publication-trace-direct-1.log').read_text()
    assert "unexpected identifier; expected ','" in (HERE / 'publication-trace-direct-2.log').read_text()
    assert len(re.findall(r'^theorem ', source, re.M)) == 1
    assert len(re.findall(r'^def ', source, re.M)) == 1
    assert source.count('obtain ⟨path,rooted⟩ := supported') == 1
    assert 'earlierIndex < index' in source
    public_type = source[source.index('theorem build_trace_writers '):].split(':= by', 1)[0]
    for private_name in ['Rooted', 'Supported', 'WrittenIn', '_private']:
        assert private_name not in public_type
    assert public_type.count('(events path)') == 4
    assert public_type.count('Reached original initial') == 3
    snippet = (HERE / 'order-helpers-snippet.lean.txt').read_text()
    assert hashlib.sha256(snippet.encode()).hexdigest() == 'c23cca308578ed9d09b80ff60637701cb21b7d36703f4b4d8511ac3f5b311a75'
    assert source.count(snippet) == 1
    old = (args.root / 'lean/MicroCFTA/SourceCurrentCompletedBuildRootedWriters.lean').read_text()
    copied = old[old.index('private def Rooted'):old.index('private theorem prepend')]
    assert copied in source
    assert (HERE / 'public-producer.lean.txt').read_text() in source
    printer = (HERE / 'publication-trace-public-1.source.lean').read_text()
    assert printer.startswith(source)
    for option in ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
                   'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']:
        assert 'set_option ' + option in printer
    for pattern in [r'^#check @', r'^#print (?!axioms )', r'^#print axioms ']:
        assert len(re.findall(pattern, printer, re.M)) == 2
    for head in HEADS:
        for directive in ['#check @', '#print ', '#print axioms ']:
            assert directive + head in printer
    log = (HERE / 'publication-trace-public-1.log').read_text()
    assert re.search(r'^theorem ' + re.escape(HEADS[1]), log, re.M)
    assert re.search(r'^def ' + re.escape(HEADS[0]), log, re.M)
    printed_type = log[log.index('theorem ' + HEADS[1]):].split(':=', 1)[0]
    assert '_private' not in printed_type
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
    assert len(reports) + len(re.findall('does not depend on any axioms', log)) == 2
    for report in reports:
        assert set(re.split(r',\s*', re.sub(r'\.\{[^}]*\}', '', report).strip())) <= {'propext', 'Classical.choice', 'Quot.sound'}
    selection = json.loads((HERE / 'publication-trace-selection.json').read_text())
    assert selection['finalized'] and selection['lean_jobs'] == 4 and selection['failed_attempts'] == 2
    assert selection['public_heads'] == HEADS and selection['canonical'] is None
    print(json.dumps({'status': 'PASS', 'pins': len(manifest['files']) + len(manifest['sources']),
                      'public_pairs': 2, 'constructed_pairs': 0, 'lean_jobs': 4,
                      'failed_attempts': 2, 'canonical_jobs': 0, 'live': args.live}))


if __name__ == '__main__':
    main()
