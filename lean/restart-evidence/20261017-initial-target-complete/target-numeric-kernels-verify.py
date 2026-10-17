#!/usr/bin/env python3
"""Verify frozen Target integration evidence without rebuilding."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
manifest = json.loads((HERE / 'target-numeric-kernels-manifest.json').read_text())
assert len(manifest['entries']) == manifest['entry_count']
seen = set()
for entry in manifest['entries']:
    assert entry['path'] not in seen, entry['path']
    seen.add(entry['path'])
    data = (ROOT / entry['path']).read_bytes()
    assert len(data) == entry['bytes'], entry['path']
    assert hashlib.sha256(data).hexdigest() == entry['sha256'], entry['path']
for path in manifest['empty_success_logs']:
    assert (ROOT / path).read_bytes() == b'', path
canonical = (ROOT / manifest['canonical_log']).read_text()
assert 'Build completed successfully (1523 jobs).' in canonical
source = (ROOT / manifest['check']['source']).read_text()
log = (ROOT / manifest['check']['log']).read_text()
assert not re.search(r'error(?:\(|:)|warning:|sorryAx', log)
pairs = re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]", log, re.M | re.S)
pairs += [(name, '') for name in re.findall(r"^'([^']+)' does not depend on any axioms$", log, re.M)]
assert len(pairs) == manifest['check']['pairs']
assert {name for name, _ in pairs} == set(manifest['check']['declarations'])
for name, axioms in pairs:
    assert '#print axioms ' + name in source
    assert '#check @' + name in source
    assert re.search(r'^@?' + re.escape(name) + r'\s*:', log, re.M), name
    names = [re.sub(r'\.\{[^}]*\}', '', item.strip()) for item in axioms.split(',') if item.strip()]
    assert set(names) <= {'propext', 'Classical.choice', 'Quot.sound'}, (name, names)
for setting in ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
                'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']:
    assert 'set_option ' + setting in source, setting
assert source.endswith('\n') and not source.endswith('\n\n')
assert (ROOT / manifest['check']['source']).read_bytes() == (ROOT / manifest['check']['snapshot']).read_bytes()
attempts = json.loads((HERE / 'target-numeric-kernels-attempts.json').read_text())['attempts']
assert len(attempts) == 7
for record in attempts:
    assert (HERE / record['source']).exists()
    assert (HERE / record['log']).exists()
    text = (HERE / record['log']).read_text()
    if record['kind'] == 'kernel' and record['attempt'] in (1, 2):
        assert text == '' and record['exit_code'] == 130
    if record['kind'] == 'kernel' and record['attempt'] == 3:
        assert 'error: unsolved goals' in text and record['exit_code'] == 130
    if record['kind'] == 'room_draft' and record['attempt'] in (1, 2):
        assert 'error:' in text and record['exit_code'] == 1
    if record['status'] == 'passed':
        assert record['exit_code'] == 0
print('PASS:', manifest['entry_count'], 'hashes;', len(pairs), 'complete pairs; diagnostics 0; all 7 attempts preserved')
