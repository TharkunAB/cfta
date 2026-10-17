#!/usr/bin/env python3
from pathlib import Path
import hashlib
import json
import re

root = Path(__file__).resolve().parents[3]
base = Path(__file__).resolve().parent
registry = json.loads((base / 'generated-query-survey-sources.json').read_text())
assert registry['source_count'] == len(registry['sources']) == 20
assert len(registry['declarations']) == 17
for item in registry['sources']:
    path = root / item['path']
    assert path.resolve().is_relative_to(root)
    raw = path.read_bytes()
    assert len(raw) == item['bytes'], path
    assert hashlib.sha256(raw).hexdigest() == item['sha256'], path
    lines = raw.decode().splitlines()
    for name, line in item['anchors'].items():
        assert re.match(r'(?:noncomputable )?(?:theorem|structure|def|inductive) ' + re.escape(name) + r'(?:\s|\[|\{|\(|$)', lines[line - 1]), (path, name)
for item in registry['declarations']:
    lines = (root / item['path']).read_text().splitlines()
    assert '\n'.join(lines[item['line'] - 1:item['last_header_line']]) + '\n' == item['source_header']
computed = root / 'lean/MicroCFTA/SourceCurrentAllocatedNativeComputedBudget.lean'
assert hashlib.sha256(computed.read_bytes()).hexdigest() == '82d4affc8d0e587504f9f8cdfaf37dc34e946d4de7e7d5f8a7a690b60e8983b8'
for suffix in ['md', 'sources.json', 'verify.py']:
    path = base / ('generated-query-survey.' + suffix if suffix == 'md' else 'generated-query-survey-' + suffix)
    raw = path.read_bytes()
    assert raw.endswith(b'\n') and not raw.endswith(b'\n\n'), path
manifest = base / 'generated-query-survey-manifest.json'
if manifest.exists():
    data = json.loads(manifest.read_text())
    assert len(data['files']) == data['file_count']
    assert data['source_count'] == 20 and data['exact_declaration_headers'] == 17
    for item in data['files']:
        path = root / item['path']
        assert path.stat().st_size == item['bytes'], path
        assert hashlib.sha256(path.read_bytes()).hexdigest() == item['sha256'], path
print('PASS: generated-query read-only survey; 20 exact source hashes and 17 declaration headers; no new completion/resource theorem claimed.')
