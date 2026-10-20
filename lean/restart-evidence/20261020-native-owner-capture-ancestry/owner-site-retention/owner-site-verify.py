import argparse
import datetime
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
ATTEMPTS = {'owner-site-direct-1': 1, 'owner-site-direct-2': 0, 'owner-site-public-1': 0}
NAME = 'MicroCFTA.SourceCurrentNativeOwnerSiteRetention.request'
FINAL_SHA = '0d9f68075df1acaee27349212adfeff70262f28fbe9a6b3404b38de16abd0894'
OPTIONS = ['linter.all true', 'pp.explicit true', 'pp.fullNames true',
           'pp.proofs true', 'pp.proofs.threshold 254', 'pp.universes true',
           'pp.deepTerms true', 'pp.maxSteps 10000000']


def check_file(base, item):
    data = (base / item['path']).read_bytes()
    assert len(data) == item['bytes'], ('bytes', item['path'])
    assert hashlib.sha256(data).hexdigest() == item['sha256'], ('sha256', item['path'])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, default=Path('/home/tritlo/Code/mcfta'))
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    manifest = json.loads((HERE / 'owner-site-manifest.json').read_text())
    for item in manifest['files']:
        check_file(HERE, item)
    for item in manifest['sources']:
        snapshot = HERE / item['snapshot']
        data = snapshot.read_bytes()
        assert len(data) == item['bytes'] and hashlib.sha256(data).hexdigest() == item['sha256'], item['path']
        if args.live:
            check_file(args.root, item)
    assert {f.stem for f in HERE.iterdir() if re.fullmatch(r'owner-site-(?:direct|public)-\d+\.json', f.name)} == set(ATTEMPTS)
    for stem, code in ATTEMPTS.items():
        meta = json.loads((HERE / (stem + '.json')).read_text())
        assert meta['exit_code'] == code and '-Dlinter.all=true' in meta['command']
        assert meta['command'][0] == '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean'
        assert Path(meta['command'][-1]).name == meta['source']
        assert hashlib.sha256((HERE / meta['source']).read_bytes()).hexdigest() == meta['sha256']
        assert json.loads((HERE / meta['limits']).read_text()) == {
            'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
        assert meta['wrapper'][meta['wrapper'].index('--mem') + 1] == '4G'
        assert meta['wrapper'][meta['wrapper'].index('--time') + 1] == '5m'
        usage = json.loads((HERE / (stem + '.usage.json')).read_text())
        assert usage['age_seconds'] < 120 and usage['remaining_percent'] > 1
        assert datetime.datetime.fromisoformat(meta['observed_at']) >= datetime.datetime.fromisoformat(meta['started_at'])
        if code:
            assert re.search(r'\berror(?:\([^)]*\))?:', (HERE / meta['log']).read_text())
    source = (HERE / 'SourceCurrentNativeOwnerSiteRetention.lean').read_bytes()
    assert hashlib.sha256(source).hexdigest() == FINAL_SHA
    assert source == (HERE / 'owner-site-direct-2.source.lean').read_bytes()
    assert not (HERE / 'owner-site-direct-2.log').read_bytes()
    assert b'_private' not in source and not re.search(rb'\b(?:sorry|axiom)\b', source)
    assert len(re.findall(rb'^theorem ', source, re.M)) == 1
    statement = source.decode().split('\ntheorem request ', 1)[1].split(' := by', 1)[0]
    assert 'SourceCurrentNativeOptionalOwnerReceipt.Owner' not in statement
    assert '(shape : Shape before.native)' in statement
    receipt = (HERE / 'inputs/SourceCurrentNativeOptionalOwnerReceipt.lean').read_text()
    expected = receipt.split('    (siteBefore : Checked width) : Prop :=\n', 1)[1].split('\n/-- Appending code', 1)[0]
    expected = expected.replace('Control A', 'Control Node').replace('Code Symbol Guard A', 'Code Symbol Guard Node')
    expected = expected.replace('Trace queryFuel control before', 'Trace queryFuel (.code (requestNode request.domain request.left request.right)) before')
    expected = expected.rstrip().replace('    siteNext = fun value => .finishNode handle value (callerNext value)',
        '    (siteNext = fun value => .finishNode handle value (callerNext value))')
    expected += ' ∧\n    siteBefore.native.nodes.cells handle = some ⟨captured, .evaluating⟩'
    assert statement.split('siteBefore) :\n', 1)[1] == expected
    assert source.count(b'SourceCurrentNativeOptionalOwner.request request fuel before siteBefore') == 1
    assert source.decode().count('obtain ⟨queryFuel, childFuel, queried') == 1
    assert b'SourceEqualityNativeDemandRunning.trace_retains childFuel' in source
    assert b'retained.2.1 handle captured childEvaluating' in source
    printer = (HERE / 'owner-site-public-1.source.lean').read_text()
    assert printer.encode().startswith(source) and printer == (HERE / 'owner-site-public.lean').read_text()
    for option in OPTIONS:
        assert 'set_option ' + option in printer
    for pattern in [r'^#check @', r'^#print (?!axioms )', r'^#print axioms ']:
        assert len(re.findall(pattern, printer, re.M)) == 1
    for directive in ['#check @', '#print ', '#print axioms ']:
        assert directive + NAME in printer
    log = (HERE / 'owner-site-public-1.log').read_text()
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    assert re.search(r'^theorem ' + re.escape(NAME), log, re.M)
    reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
    assert len(reports) + len(re.findall(r'does not depend on any axioms', log)) == 1
    for report in reports:
        assert set(re.split(r',\s*', re.sub(r'\.\{[^}]*\}', '', report).strip())) <= {'propext', 'Classical.choice', 'Quot.sound'}
    selection = json.loads((HERE / 'owner-site-selection.json').read_text())
    assert selection['finalized'] and selection['public_heads'] == [NAME]
    assert selection['attempts'] == list(ATTEMPTS) and selection['strict'] == 'owner-site-direct-2'
    assert selection['groups'] == [{'name': 'owner-site-public-1', 'pairs': 1, 'kind': 'prototype-public', 'full_proof': True}]
    assert selection['lean_jobs'] == 3 and selection['failed_attempts'] == 1
    assert selection['production_pairs'] == 1 and selection['constructed_pairs'] == 0
    assert selection['canonical'] is None and selection['canonical_jobs'] == 0
    peaks = (HERE / 'owner-site-peaks-final.txt').read_text().splitlines()
    assert len(peaks) == len(ATTEMPTS)
    assert [int(line.split()[-1]) for line in peaks] == list(ATTEMPTS.values())
    assert all(line.split()[2] == '4G' for line in peaks)
    print(json.dumps({'status': 'PASS', 'pins': len(manifest['files']) + len(manifest['sources']),
                      'public_pairs': 1, 'constructed_pairs': 0, 'lean_jobs': 3,
                      'failed_attempts': 1, 'canonical_jobs': 0,
                      'mode': 'live' if args.live else 'ordinary'}))


if __name__ == '__main__':
    main()
