"""Verify read-only review pins and the corrected strict/public selections."""
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
pins = json.loads((HERE / 'independent-paired-ordinary-review-pins.json').read_text())
for entry in pins['files']:
    data = (ROOT / entry['path']).read_bytes()
    assert len(data) == entry['bytes'], entry['path']
    assert hashlib.sha256(data).hexdigest() == entry['sha256'], entry['path']
limits = {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
for stem in pins['selected_runs']:
    run = json.loads((HERE / (stem + '.json')).read_text())
    assert run['exit_code'] == 0, stem
    assert json.loads((HERE / run['limits']).read_text()) == limits, stem
    if 'source' in run:
        source = HERE / run['source']
        assert hashlib.sha256(source.read_bytes()).hexdigest() == run['sha256'], stem
        assert run['command'][-1] == str(source), stem
for stem in ['paired-ordinary-direct-3', 'paired-ordinary-kernels-5']:
    assert (HERE / (stem + '.log')).read_bytes() == b'', stem
source = (HERE / 'paired-ordinary-public-2.source.lean').read_text()
output = (HERE / 'paired-ordinary-public-2.log').read_text()
for option in ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
               'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']:
    assert 'set_option ' + option in source
assert len(re.findall(r'^#check @', source, re.M)) == 6
assert len(re.findall(r'^#print (?!axioms )', source, re.M)) == 6
assert len(re.findall(r'^#print axioms ', source, re.M)) == 6
assert not re.search(r'warning:|error:|error\(|sorryAx|failed to pretty print|maximum recursion|deterministic timeout|⋯|…', output, re.I)
reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', output)
assert len(reports) + len(re.findall('does not depend on any axioms', output)) == 6
for report in reports:
    clean = re.sub(r'\.\{[^}]*\}', '', report)
    assert {part.strip() for part in clean.split(',')} <= {'propext', 'Classical.choice', 'Quot.sound'}
assert (ROOT / 'lean/MicroCFTA/SourceCurrentStoredPairedOrdinaryLineage.lean').read_bytes() == (HERE / 'paired-ordinary-direct-3.source.lean').read_bytes()
assert len((HERE / 'paired-ordinary-direct-2.log').read_bytes()) == 1079
assert 'failed to pretty print' in (HERE / 'paired-ordinary-kernels-public-1.log').read_text()
assert json.loads((HERE / 'paired-ordinary-kernels-public-2.json').read_text())['exit_code'] == -15
print(f"PASS: {len(pins['files'])} review pins; corrected strict and kernel logs empty; six full public pairs; earlier warnings and printer attempts retained; no repeated Lean execution.")
