#!/usr/bin/env python3
"""Check immutable source and proof receipts without running Lean."""
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
manifest = json.loads((HERE / 'leaf-call-manifest.json').read_text())
for item in manifest['files']:
    path = (HERE if item['base'] == 'here' else ROOT) / item['path']
    data = path.read_bytes()
    assert len(data) == item['bytes'], (item['path'], 'bytes')
    assert hashlib.sha256(data).hexdigest() == item['sha256'], (item['path'], 'sha256')
selection = json.loads((HERE / 'leaf-call-selection.json').read_text())
expected_codes = [1, 0, 1, 1, 1, 0, 0]
assert selection['owned_jobs'] == len(selection['attempts']) == len(expected_codes) == 7
for stem, code in zip(selection['attempts'], expected_codes):
    receipt = json.loads((HERE / (stem + '.json')).read_text())
    assert receipt['exit_code'] == code, (stem, 'exit')
    source = HERE / receipt['source']
    assert hashlib.sha256(source.read_bytes()).hexdigest() == receipt['sha256'], stem
    assert receipt['command'][-1] == '/tmp/mcfta-open-ordinary-leaf-source-calls/' + source.name
    assert receipt['command'][-2] == '-Dlinter.all=true'
    assert receipt['wrapper'][1:5] == ['--mem', '4G', '--time', '5m']
    limits = json.loads((HERE / receipt['limits']).read_text())
    assert limits == {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}, stem
    usage = json.loads((HERE / (stem + '.usage.json')).read_text())
    assert usage['age_seconds'] < 120 and usage['remaining_percent'] > 1, stem
    if code:
        assert (HERE / receipt['log']).stat().st_size > 0, stem
strict = selection['selected_strict']
strict_receipt = json.loads((HERE / (strict + '.json')).read_text())
assert strict_receipt['exit_code'] == 0
assert (HERE / strict_receipt['log']).read_bytes() == b''
candidate = (HERE / selection['production_candidate']).read_bytes()
assert candidate == (HERE / strict_receipt['source']).read_bytes()
assert not re.search(rb'\b(?:sorry|admit)\b', candidate)
assert len(re.findall(rb'^theorem ', candidate, re.M)) == 1
qualified = 'MicroCFTA.SourceCurrentOpenOrdinaryLeafSourceCalls.node_leaf'
assert selection['public_declarations'] == [qualified]
assert selection['owned_public_pairs'] == 1 and selection['owned_constructed_pairs'] == 0
assert selection['canonical'] is None
public_receipt = json.loads((HERE / 'leaf-call-public-1.json').read_text())
public_source = (HERE / public_receipt['source']).read_bytes()
assert public_source.startswith(candidate)
for option in ['pp.explicit true', 'pp.fullNames true', 'pp.proofs true', 'pp.proofs.threshold 254',
               'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000', 'linter.all true']:
    assert ('set_option ' + option).encode() in public_source, option
for command in ['#check @', '#print ', '#print axioms ']:
    assert (command + qualified).encode() in public_source, command
log = (HERE / public_receipt['log']).read_text()
assert public_receipt['exit_code'] == 0
assert log.startswith('@' + qualified + ' :')
assert 'theorem ' + qualified in log
assert not re.search(r'(?:warning:|error:|sorryAx|failed to pretty|maximum recursion|maximum number of steps|heartbeat|\.\.\.|…)', log, re.I)
axioms = re.findall("'" + re.escape(qualified) + r"' depends on axioms: \[(.*?)\]", log, re.S)
assert len(axioms) == 1
axiom_names = re.sub(r'\.\{[^}]*\}', '', axioms[0])
assert {name.strip() for name in axiom_names.split(',')} == {'propext', 'Classical.choice', 'Quot.sound'}
peaks = (HERE / 'leaf-call-peaks-final.txt').read_text().splitlines()
assert len(peaks) == 7
assert [int(line.split()[-1]) for line in peaks] == expected_codes
assert all(' 4G ' in line for line in peaks)
print(json.dumps({'status': 'PASS', 'files': len(manifest['files']), 'owned_jobs': 7,
                  'selected_public_pairs': 1, 'constructed_pairs': 0,
                  'strict_log_bytes': 0, 'full_proof_log_bytes': len(log.encode()),
                  'standard_axioms_only': True, 'canonical_run': False}, sort_keys=True))
