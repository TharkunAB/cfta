#!/usr/bin/env python3
"""Verify the selected editor review receipts without running Lean."""
import hashlib
import json
import re
from pathlib import Path

ROOT = Path('/home/tritlo/Code/mcfta')
HERE = Path(__file__).resolve().parent
manifest = json.loads((HERE / 'editor-cross-review-manifest.json').read_text())
for entry in manifest['entries']:
    data = (ROOT / entry['path']).read_bytes()
    assert len(data) == entry['bytes'], entry['path']
    assert hashlib.sha256(data).hexdigest() == entry['sha256'], entry['path']

selection = json.loads((HERE / 'editor-cross-review-selection.json').read_text())
assert selection['review_only'] is True
assert selection['new_public_pairs'] == selection['new_constructed_pairs'] == 0
assert selection['reviewed_existing_public_pairs'] == 17
limits = {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
toolchain = '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/'
wrapper = ['/home/tritlo/Code/heavy-management/bin/capped', '--mem', '4G', '--time', '5m']
options = ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
           'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']
bad_text = ['sorryAx', 'failed to pretty print', '⋯', '…', '...', 'truncated',
            'error:', 'warning:', 'error(', 'warning(', 'maximum recursion depth',
            'maximum number of heartbeats', 'pp.rawOnError']


def receipt(stem: str, canonical: bool = False) -> tuple[dict, str]:
    record = json.loads((HERE / (stem + '.json')).read_text())
    assert record['exit_code'] == 0, stem
    assert json.loads((HERE / record['limits']).read_text()) == limits, stem
    assert record['wrapper'][:5] == wrapper, stem
    assert record['log'] == stem + '.log', stem
    if not canonical:
        snapshot = HERE / record['source']
        assert snapshot.name == stem + '.source.lean', stem
        assert record['command'] == [toolchain + 'lean', '-Dlinter.all=true', str(snapshot)], stem
        assert hashlib.sha256(snapshot.read_bytes()).hexdigest() == record['sha256'], stem
    return record, (HERE / record['log']).read_text()


total = 0
for group in selection['selected_existing_groups']:
    production = ROOT / group['production']
    data = production.read_bytes()
    assert hashlib.sha256(data).hexdigest() == group['production_sha256']
    strict, output = receipt(group['strict'])
    assert output == '', group['strict']
    assert data == (HERE / strict['source']).read_bytes(), group['strict']
    canonical, output = receipt(group['canonical'], canonical=True)
    assert canonical['command'] == [toolchain + 'lake', '-d', str(ROOT / 'lean'), 'build',
                                     'MicroCFTA.' + production.stem]
    assert 'Build completed successfully' in output, group['canonical']
    assert production.name + ':' not in output, group['canonical']
    public, output = receipt(group['public'])
    source = (HERE / public['source']).read_text()
    for option in options:
        assert 'set_option ' + option in source, (group['public'], option)
    heads = re.findall(r'^#check @([^\s]+)$', source, re.M)
    assert len(heads) == group['pairs'], group['public']
    assert len(re.findall(r'^#print (?!axioms )', source, re.M)) == len(heads)
    assert len(re.findall(r'^#print axioms ', source, re.M)) == len(heads)
    for head in heads:
        assert '#print ' + head + '\n' in source, head
        assert '#print axioms ' + head + '\n' in source, head
    for bad in bad_text:
        assert bad not in output, (group['public'], bad)
    reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output)
    reports += [(head, '') for head in re.findall(r"'([^']+)' does not depend on any axioms", output)]
    assert len(reports) == len(heads) and {head for head, _ in reports} == set(heads)
    for head, axioms in reports:
        plain = re.sub(r'\.\{[^}]*\}', '', axioms)
        names = {name.strip() for name in plain.split(',') if name.strip()}
        assert names <= {'propext', 'Classical.choice', 'Quot.sound'}, (head, axioms)
    total += len(heads)
assert total == 17
print(json.dumps({'status': 'PASS', 'entries': len(manifest['entries']),
                  'reviewed_existing_public_pairs': total, 'new_public_pairs': 0,
                  'new_constructed_pairs': 0, 'strict_logs_empty': 3,
                  'effective_memory_bytes': 4294967296, 'effective_swap_bytes': 0,
                  'lean_runs_by_review': 0}))
