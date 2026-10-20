#!/usr/bin/env python3
"""Check the immutable actual indexed cut witness and its proof receipts."""
from pathlib import Path
import argparse
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
parser = argparse.ArgumentParser()
parser.add_argument('--root', type=Path)
args = parser.parse_args()
default_root = HERE.parents[2] if len(HERE.parents) > 2 else Path.cwd()
ROOT = (args.root or default_root).resolve()
manifest = json.loads((HERE / 'cut-fixture-manifest.json').read_text())
for item in manifest['files']:
    path = (HERE if item['base'] == 'here' else ROOT) / item['path']
    data = path.read_bytes()
    assert len(data) == item['bytes'], (item['path'], 'bytes')
    assert hashlib.sha256(data).hexdigest() == item['sha256'], (item['path'], 'sha256')
selection = json.loads((HERE / 'cut-fixture-selection.json').read_text())
codes = [1, 1, 0, 0]
assert selection['owned_jobs'] == len(selection['attempts']) == 4
for stem, code in zip(selection['attempts'], codes):
    receipt = json.loads((HERE / (stem + '.json')).read_text())
    assert receipt['exit_code'] == code, stem
    assert hashlib.sha256((HERE / receipt['source']).read_bytes()).hexdigest() == receipt['sha256'], stem
    assert receipt['command'][-1] == '/tmp/mcfta-indexed-first-ordinary-cut-fixture/' + receipt['source']
    assert receipt['command'][-2] == '-Dlinter.all=true'
    assert receipt['wrapper'][1:5] == ['--mem', '4G', '--time', '5m']
    assert json.loads((HERE / receipt['limits']).read_text()) == {
        'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}, stem
    usage = json.loads((HERE / (stem + '.usage.json')).read_text())
    assert usage['age_seconds'] < 120 and usage['remaining_percent'] > 1, stem
    if code:
        assert (HERE / receipt['log']).stat().st_size > 0
strict = json.loads((HERE / (selection['selected_strict'] + '.json')).read_text())
assert (HERE / strict['log']).read_bytes() == b''
source = (HERE / selection['constructed_source']).read_text()
assert source == (HERE / strict['source']).read_text()
assert not re.search(r'\b(?:sorry|admit)\b', source)
assert len(re.findall(r'^theorem ', source, re.M)) == 1
private_statement = source.split('private theorem checked_witness :\n', 1)[1].split(' := by', 1)[0]
public_statement = source.split('theorem actual_prefixes :\n', 1)[1].split(' := checked_witness', 1)[0]
assert private_statement == public_statement
assert source.count('SourceCurrentIndexedLeafSourceRows.source_cases') == 1
assert 'SourceRow source inputs (empty : Heap) raw wholeRun.state row' in public_statement
assert 'Cut raw 4 leaf parentRow 3 leaf 0' in public_statement
assert '(leaves raw)[1]? = some leaf' in public_statement
assert '(leaves raw)[4]? = some leaf' in public_statement
assert 'row ≠ leafRow' in public_statement
assert 'Context (empty : Heap) inputs' in public_statement
qualified = 'MicroCFTA.IndexedFirstOrdinaryCutKernels.actual_prefixes'
assert selection['public_declarations'] == [qualified]
assert selection['owned_public_pairs'] == 0 and selection['owned_constructed_pairs'] == 1
assert selection['canonical'] is None
receipt = json.loads((HERE / 'cut-fixture-public-1.json').read_text())
public = (HERE / receipt['source']).read_text()
assert public.startswith(source)
for option in ['pp.explicit true', 'pp.fullNames true', 'pp.proofs true', 'pp.proofs.threshold 254',
               'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000', 'linter.all true']:
    assert 'set_option ' + option in public, option
for command in ['#check @', '#print ', '#print axioms ']:
    assert command + qualified in public, command
log = (HERE / receipt['log']).read_text()
assert log.startswith(qualified + ' :') or log.startswith('@' + qualified + ' :')
assert 'theorem ' + qualified in log
assert qualified.rsplit('.', 1)[0] + '.checked_witness' in log
assert not re.search(r'(?:warning:|error:|sorryAx|failed to pretty|maximum recursion|maximum number of steps|heartbeat|\.\.\.|…)', log, re.I)
axiom_lists = re.findall("'" + re.escape(qualified) + r"' depends on axioms: \[(.*?)\]", log, re.S)
assert len(axiom_lists) == 1
axiom_text = re.sub(r'\.\{[^}]*\}', '', axiom_lists[0])
axioms = {item.strip() for item in axiom_text.split(',')}
assert axioms == {'propext', 'Classical.choice', 'Quot.sound'}
assert axioms <= {'propext', 'Classical.choice', 'Quot.sound'}
peaks = (HERE / 'cut-fixture-peaks-final.txt').read_text().splitlines()
assert len(peaks) == 4
assert [int(line.split()[-1]) for line in peaks] == codes
assert all(' 4G ' in line for line in peaks)
print(json.dumps({'status': 'PASS', 'files': len(manifest['files']), 'owned_jobs': 4,
                  'production_pairs': 0, 'constructed_pairs': 1, 'strict_log_bytes': 0,
                  'full_proof_log_bytes': len(log.encode()), 'standard_axioms_only': True,
                  'canonical_run': False, 'runtime_defect_claimed': False}, sort_keys=True))
