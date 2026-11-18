from pathlib import Path
import datetime
import hashlib
import json
import shutil
from zoneinfo import ZoneInfo

ROOT = Path('/home/tritlo/Code/mcfta')
BASE = ROOT / 'lean/restart-evidence'
OLD = BASE / '20261118-actual-dispatch-source-seeds-transition-draft'
INCOMING = BASE / '20261118-actual-incoming-source-seeds-normalization-repair'
NEW = BASE / '20261118-actual-dispatch-source-seeds-normalization-rebase'
SHA = lambda data: hashlib.sha256(data).hexdigest()
assert not NEW.exists()
assert SHA((OLD / 'MANIFEST.json').read_bytes()) == '1f6368c3eac1e8aab8132a340b969b55ea951d362ec8eb8ba7f6796cf9b4afbe'
assert SHA((INCOMING / 'MANIFEST.json').read_bytes()) == 'a59189f26b8a8efa375a1dcc19167121365c21b23f8cb5cd78802b13ae8d04e2'
for packet in [OLD, INCOMING]:
    for item in json.loads((packet / 'MANIFEST.json').read_text())['files']:
        data = (packet / item['file']).read_bytes()
        assert len(data) == item['bytes'] and SHA(data) == item['sha256']
shutil.copytree(OLD, NEW)
(NEW / 'MANIFEST.json').unlink()
for old, new in [('STATIC-VALIDATION.json', 'HISTORICAL-STATIC-VALIDATION.json'),
                 ('DEPENDENCIES.json', 'HISTORICAL-DEPENDENCIES.json')]:
    (NEW / old).rename(NEW / new)
assembly = json.loads((OLD / 'ASSEMBLY.json').read_text())
source = assembly['source']
imports = (OLD / 'IMPORTS.lean.txt').read_bytes()
incoming = (INCOMING / source).read_bytes()
appended = (OLD / 'APPEND.lean.txt').read_bytes()
assert len(imports) == 75 and len(appended) == 13793
raw = imports + incoming + appended
(NEW / source).write_bytes(raw)
now = datetime.datetime.now(ZoneInfo('Europe/Stockholm')).isoformat()
assembly.update(raw_sha256=SHA(raw), raw_bytes=len(raw), raw_lines=len(raw.splitlines()),
                base_packet=str(INCOMING.relative_to(ROOT)),
                base_manifest_sha256=SHA((INCOMING / 'MANIFEST.json').read_bytes()),
                base_raw_sha256=SHA(incoming), base_bytes=len(incoming),
                status='FROZEN EXACT DISPATCH APPEND REBASE; UNCOMPILED; ZERO CREDIT')
(NEW / 'ASSEMBLY.json').write_text(json.dumps(assembly, indent=2) + '\n')
unchanged = ['APPEND.lean.txt', 'FIRST-HEADER.lean.txt', 'HEADER-FREEZE.json', 'IMPORTS.lean.txt',
             'PREAMBLE.lean.txt', 'PROOF.lean.txt', 'PROBES.lean.txt', 'COMBINED-PROBES.lean.txt']
for name in unchanged:
    assert (NEW / name).read_bytes() == (OLD / name).read_bytes()
(NEW / 'REBASE.json').write_text(json.dumps({
    'at': now, 'original_packet': OLD.name,
    'original_manifest_sha256': SHA((OLD / 'MANIFEST.json').read_bytes()),
    'selected_incoming_packet': INCOMING.name,
    'selected_incoming_manifest_sha256': SHA((INCOMING / 'MANIFEST.json').read_bytes()),
    'selected_incoming_raw_sha256': SHA(incoming), 'selected_incoming_bytes': len(incoming),
    'incoming_entire_contiguous_offset': 75,
    'dispatch_source_files_byte_exact': unchanged,
    'all_incoming_headers_private_bodies_preserved_by_base_repair': True,
    'dispatch_proof_and_FIRST_unchanged': True,
    'new_public_reports': 1, 'combined_public_reports': 2,
    'retained_private_helpers_transitive': 2, 'new_private_helpers': 0, 'new_definitions': 0,
    'proof_credit': 0, 'normal_Source_changed': False,
}, indent=2) + '\n')
pins = {str((INCOMING / name).relative_to(ROOT)): SHA((INCOMING / name).read_bytes())
        for name in ['MANIFEST.json', source, 'FIRST-HEADER.lean.txt', 'QUERY-FIRST.lean.txt',
                     'TRACE-GROWTH-FIRST.lean.txt', 'PROOF-REPAIR.json']}
(NEW / 'CURRENT-BASE-PINS.json').write_text(json.dumps(pins, indent=2) + '\n')
(NEW / 'DEPENDENCIES.json').write_text(json.dumps({
    'incoming_base_packet': INCOMING.name,
    'incoming_manifest_sha256': SHA((INCOMING / 'MANIFEST.json').read_bytes()),
    'incoming_raw_sha256': SHA(incoming), 'incoming_checked': False,
    'historical_input_metadata_retained': ['SOURCE-PINS.json', 'HISTORICAL-DEPENDENCIES.json'],
    'dispatch_append_sha256': SHA(appended), 'proof_credit': 0,
}, indent=2) + '\n')
(NEW / 'STATIC-VALIDATION.json').write_text(json.dumps({
    'status': 'STATIC ONLY; NOT COMPILED', 'assembly_exact': True,
    'entire_incoming_module_preserved': True, 'incoming_bytes': len(incoming),
    'incoming_offset': 75, 'dispatch_append_byte_exact': True,
    'dispatch_FIRST_and_proof_byte_exact': True, 'combined_public_reports': 2,
    'retained_private_helpers_transitive': 2, 'new_definitions': 0,
    'normal_Source_changed': False,
}, indent=2) + '\n')
(NEW / 'README.md').write_text('''# Dispatch Seeds: rebase on the incoming normalization repair

This packet is uncompiled and has zero theorem credit.
It retains the complete selected incoming module after the 75-byte import.
The dispatch append, proof, FIRST and probes remain byte-exact.
The incoming base resolves NodeRequest and the skipped-check Boolean simplification.
The original dispatch candidate and original incoming variants remain unchanged.
Historical metadata files describe the original base only.
The current base is bound by CURRENT-BASE-PINS.json and ASSEMBLY.json.
Original fuels, premises, conclusions and proof limits stay unchanged.
Whole-worker Seeds and joint finite completion remain open.
''')
files = [{'file': str(path.relative_to(NEW)), 'bytes': path.stat().st_size, 'sha256': SHA(path.read_bytes())}
         for path in sorted(NEW.rglob('*')) if path.is_file()]
(NEW / 'MANIFEST.json').write_text(json.dumps({'status': assembly['status'], 'frozen_at': now,
                                             'files': files}, indent=2) + '\n')
print(json.dumps({'packet': NEW.name, 'manifest_sha256': SHA((NEW / 'MANIFEST.json').read_bytes()),
                  'raw_sha256': SHA(raw), 'raw_bytes': len(raw)}))
