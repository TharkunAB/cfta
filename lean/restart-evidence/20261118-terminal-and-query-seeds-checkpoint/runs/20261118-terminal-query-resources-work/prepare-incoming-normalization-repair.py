from pathlib import Path
import datetime
import difflib
import hashlib
import json
import shutil
from zoneinfo import ZoneInfo

ROOT = Path('/home/tritlo/Code/mcfta')
BASE = ROOT / 'lean/restart-evidence'
OLD = BASE / '20261118-actual-incoming-source-seeds-enumeration-scope-repair'
NEW = BASE / '20261118-actual-incoming-source-seeds-normalization-repair'
SHA = lambda data: hashlib.sha256(data).hexdigest()
assert not NEW.exists()
assert SHA((OLD / 'MANIFEST.json').read_bytes()) == '48eac8272a03c0797fdd76929c8ddc587057357af6f08b40d8f5af0ee150bddc'
for item in json.loads((OLD / 'MANIFEST.json').read_text())['files']:
    data = (OLD / item['file']).read_bytes()
    assert len(data) == item['bytes'] and SHA(data) == item['sha256']
failed = BASE / '20261118-incoming-query-seeds-check'
rejection = json.loads((Path(__file__).parent / 'INCOMING-SEEDS-FIRST-CHECK-REJECTED.json').read_text())
assert rejection['actual_session'] == 54752 and rejection['actual_terminal_exit'] == 1
assert rejection['credited_public_reports'] == 0 and not (failed / 'checked.json').exists()
for name, digest in json.loads((failed / 'source-pins.json').read_text()).items():
    assert SHA((ROOT / name).read_bytes()) == digest, name
shutil.copytree(OLD, NEW)
(NEW / 'MANIFEST.json').unlink()
for before, after in [('REPAIR.json', 'HISTORICAL-SCOPE-REPAIR.json'),
                      ('STATIC-VALIDATION.json', 'HISTORICAL-SCOPE-STATIC-VALIDATION.json'),
                      ('SOURCE-DIFF.patch', 'HISTORICAL-SCOPE-DIFF.patch')]:
    (NEW / before).rename(NEW / after)
preamble = (OLD / 'PREAMBLE.lean.txt').read_bytes()
anchor = b'open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionControl SourceRecursiveIntersectionCode\n'
added = b'open SourceRecursiveIntersectionThunks (NodeRequest)\n'
assert preamble.count(anchor) == 1
(NEW / 'PREAMBLE.lean.txt').write_bytes(preamble.replace(anchor, added + anchor, 1))
proof = (OLD / 'PROOF.lean.txt').read_bytes()
before = b'nativeRead, \xe2\x86\x93reduceIte,\n                                    skip.2.1'
after = b'nativeRead, Bool.false_eq_true, \xe2\x86\x93reduceIte,\n                                    skip.2.1'
assert proof.count(before) == 1
(NEW / 'PROOF.lean.txt').write_bytes(proof.replace(before, after, 1))
assembly = json.loads((OLD / 'ASSEMBLY.json').read_text())
raw = b''.join((NEW / part).read_bytes() if (NEW / part).is_file() else part.encode()
               for part in assembly['assembly'])
source = assembly['source']
original_raw = (OLD / source).read_bytes()
assert raw == original_raw.replace(anchor, added + anchor, 1).replace(before, after, 1)
(NEW / source).write_bytes(raw)
unchanged = ['FIRST-HEADER.lean.txt', 'TRACE-GROWTH-FIRST.lean.txt', 'QUERY-FIRST.lean.txt',
             'TRACE-GROWTH-PROOF.lean.txt', 'QUERY-PROOF.lean.txt', 'HEADER-FREEZE.json',
             'PROBES.lean.txt', 'INTERNAL-PROBES.lean.txt']
for name in unchanged:
    assert (NEW / name).read_bytes() == (OLD / name).read_bytes()
now = datetime.datetime.now(ZoneInfo('Europe/Stockholm')).isoformat()
assembly.update(raw_sha256=SHA(raw), raw_bytes=len(raw), raw_lines=len(raw.splitlines()),
                status='FROZEN NORMALIZATION REPAIR; UNCOMPILED; ZERO CREDIT',
                prior_scope_packet=OLD.name, prior_scope_manifest_sha256=SHA((OLD / 'MANIFEST.json').read_bytes()),
                proof_bodies_and_FIRSTs_byte_exact=False, all_FIRST_headers_byte_exact=True,
                both_private_proof_bodies_byte_exact=True, public_proof_changed_one_simp_argument=True)
(NEW / 'ASSEMBLY.json').write_text(json.dumps(assembly, indent=2) + '\n')
comparison = {
    'at': now, 'original_packet': OLD.name,
    'original_manifest_sha256': SHA((OLD / 'MANIFEST.json').read_bytes()),
    'original_raw_sha256': SHA(original_raw), 'selected_packet': NEW.name,
    'selected_raw_sha256': SHA(raw), 'source': source,
    'only_replacements': [{'old': anchor.decode(), 'new': (added + anchor).decode(), 'count': 1},
                          {'old': before.decode(), 'new': after.decode(), 'count': 1}],
    'FIRST_private_proof_and_probe_files_byte_exact': unchanged,
    'failed_actual_session': 54752, 'failed_proof_credit': 0,
    'failed_generated_sorryAx_rejected': True,
    'branch': 'checkEmpty=true after the proved skipped check returns false',
    'premises_or_conclusion_changed': False, 'proof_limits_changed': False,
    'new_public_reports': 1, 'private_helpers_transitive': 2, 'new_definitions': 0,
}
(NEW / 'PROOF-REPAIR.json').write_text(json.dumps(comparison, indent=2) + '\n')
diff = ''.join(difflib.unified_diff(original_raw.decode().splitlines(True), raw.decode().splitlines(True),
                                  fromfile=OLD.name + '/' + source, tofile=NEW.name + '/' + source))
(NEW / 'SOURCE-DIFF.patch').write_text(diff)
paths = [failed / name for name in ['results.json', 'source-pins.json', source.replace('.lean', '.txt')]]
paths += [Path(__file__).parent / name for name in ['INCOMING-SEEDS-FIRST-CHECK-REJECTED.json',
                                                  'INCOMING-SEEDS-CHECK-ACTUAL-RUN.json']]
(NEW / 'FAILED-CHECK-PINS.json').write_text(json.dumps({str(path.relative_to(ROOT)): SHA(path.read_bytes())
                                                       for path in paths}, indent=2) + '\n')
(NEW / 'STATIC-VALIDATION.json').write_text(json.dumps({
    'status': 'STATIC ONLY; NOT COMPILED', 'assembly_exact': True,
    'all_three_FIRST_headers_exact': True, 'both_private_proof_bodies_exact': True,
    'public_proof_changed_one_simp_argument': True, 'preamble_added_one_selective_open': True,
    'original_scope_repair_preserved': True, 'failed54752_credit': 0,
    'source_pins_reverified': len(json.loads((failed / 'source-pins.json').read_text())),
    'normal_Source_changed': False, 'new_definitions': 0,
}, indent=2) + '\n')
(NEW / 'README.md').write_text('''# Incoming source Seeds: namespace and Boolean normalization repair

This packet is uncompiled and has zero theorem credit.
It preserves the original scope repair and failed check 54752.
One selective open resolves NodeRequest in the private query proof.
One simp argument reduces the false result of the skipped check in the checkEmpty=true branch.
All three FIRST headers and both private proof bodies remain exact.
The original fuels, premises, conclusions and proof limits stay unchanged.
The generated sorryAx in the failed run remains rejected.
The files named HISTORICAL-SCOPE retain claims about the earlier scope repair only.
No normal Source, Git or compiler operation is performed by this packet preparer.
''')
files = [{'file': str(path.relative_to(NEW)), 'bytes': path.stat().st_size, 'sha256': SHA(path.read_bytes())}
         for path in sorted(NEW.rglob('*')) if path.is_file()]
(NEW / 'MANIFEST.json').write_text(json.dumps({'status': assembly['status'], 'frozen_at': now,
                                             'files': files}, indent=2) + '\n')
print(json.dumps({'packet': NEW.name, 'manifest_sha256': SHA((NEW / 'MANIFEST.json').read_bytes()),
                  'raw_sha256': SHA(raw), 'raw_bytes': len(raw), 'source_increase': len(raw) - len(original_raw)}))
