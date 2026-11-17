from pathlib import Path
import hashlib
import json
import re
import subprocess

ROOT = Path('/home/tritlo/Code/mcfta')
BASE = ROOT / 'lean/restart-evidence'
WORK = Path(__file__).resolve().parent
CONTROL = BASE / '20261117-warm-semantic-finish-unused-let-repair-check-control-draft'
SHA = lambda data: hashlib.sha256(data).hexdigest()
selection = json.loads((CONTROL / 'SELECTION.json').read_text())
run = BASE / selection['runtime']
receipt = json.loads((WORK / 'SIX-MODULE-UNUSED-LET-REPAIR-VERIFIED.json').read_text())
report = json.loads((run / 'checked.json').read_text())
assert receipt['actual_terminal'] and receipt['actual_terminal_exit'] == 0
assert receipt['checks'] == report['checks'] and report['six_modules_checked']
assert report['actual_public_axiom_reports'] == 5
assert report['actual_definition_declaration_checks'] == 3
assert len(report['checks']) == 6 and all(report['passed'])
assert not report['joint_finite_completion_proved'] and not report['haskell_changed']
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT).decode().strip() == 'd3ef89aa1341085317a8d6f8d0ecb327c36f0d7b'
assert not subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=no'], cwd=ROOT)
for name, digest in json.loads((run / 'source-pins.json').read_text()).items():
    assert SHA((ROOT / name).read_bytes()) == digest, name
baseline = json.loads((WORK / 'baseline-source-pins.json').read_text())
assert len(baseline) == 6258
for name, digest in baseline.items():
    assert SHA((ROOT / name).read_bytes()) == digest, name
old_audit = (WORK / 'Audit-BEFORE.lean.txt').read_bytes()
assert old_audit == (ROOT / 'lean/MicroCFTA/Audit.lean').read_bytes()
assert len(old_audit) == 428472 and old_audit.count(b'#print axioms ') == 690
components = []
imports = b''
probes = b''
private_count = 0
public_count = 0
definition_count = 0
for item in selection['components']:
    packet = BASE / item['packet']
    assert SHA((packet / 'MANIFEST.json').read_bytes()) == item['manifest_sha256']
    raw = (packet / item['source']).read_bytes()
    header = (packet / item['header']).read_bytes()
    probe = (packet / item['probe']).read_bytes()
    assert SHA(raw) == item['raw_sha256']
    assert SHA(header) == item['header_sha256'] and header.rstrip(b'\n') in raw
    assert SHA(probe) == item['probe_sha256']
    assert (run / 'source/MicroCFTA' / (item['module'] + '.lean')).read_bytes() == raw + b'\n' + probe
    target = ROOT / 'lean/MicroCFTA' / (item['module'] + '.lean')
    assert not target.exists() and not target.is_symlink()
    public = re.findall(r'^theorem (\w+)', raw.decode(), re.M)
    private = re.findall(r'^private theorem (\w+)', raw.decode(), re.M)
    definitions = re.findall(r'^def (\w+)', raw.decode(), re.M)
    assert len(public) == item['expected_axiom_reports']
    assert len(definitions) == item['expected_declaration_checks']
    qnames = re.findall(r'^#print axioms (\S+)', probe.decode(), re.M)
    assert len(qnames) == len(public)
    components.append(dict(item, source_path=str(target.relative_to(ROOT)), raw_bytes=len(raw),
                           names=qnames, new_private_helper_names=private, new_definition_names=definitions))
    private_count += len(private)
    public_count += len(public)
    definition_count += len(definitions)
    imports += ('import MicroCFTA.' + item['module'] + '\n').encode()
    probes += probe
assert len(components) == 6 and (private_count, public_count, definition_count) == (30, 5, 3)
assert imports.count(b'import ') == 6 and probes.count(b'#print axioms ') == 5
assert probes.count(b'#check ') == 3
stage = {'prior_checkpoint': 'd3ef89aa1341085317a8d6f8d0ecb327c36f0d7b',
    'source_baseline': selection['source_commit'], 'private_run': selection['runtime'],
    'components': components, 'baseline_overrides': {'lean/MicroCFTA/Audit.lean':
        str((WORK / 'Audit-BEFORE.lean.txt').relative_to(ROOT))},
    'source_files': 6264, 'audit_imports': 5264, 'audit_reports': 695,
    'independent_reports': 290, 'new_modules': 6, 'changed_existing_owners': 0,
    'new_public_theorems': 5, 'new_private_helpers': 30, 'new_theorem_declarations': 35,
    'new_prop_definitions': 3, 'fresh_reports': 5, 'inherited_reports': 484,
    'combined_reports': 489, 'old_source_files_byte_exact': 6257,
    'old_audit_bytes': len(old_audit), 'old_audit_sha256': SHA(old_audit),
    'old_audit_exact_offset': len(imports), 'new_audit_imports': 6,
    'original_C_M_edge_history_headers_exact': True,
    'original_af8_header_exact': False, 'original_af8_header_preserved': True,
    'original_af8_header_alpha_only_unused_let_rename': True,
    'original_af8_logical_type_unchanged': True,
    'all_old_proof_bodies_and_limits_unchanged': True,
    'source_semantic_finish_callbacks_proved': True,
    'source_warm_cm_returned_at_every_actual_prefix_proved': True,
    'full_actual_body_pattern_child_pair_absence_proved': True,
    'all_new_formal_proof_checks_first_pass': False,
    'notation_only_mixed_repair': True, 'warm_query_no_new_mu_proved': False,
    'every_warm_worker_call_qualification_proved': False,
    'joint_finite_completion_proved': False, 'haskell_changed': False}
for name in ['SOURCES-NORMAL-STAGING.json', 'IMPORTS.lean.txt', 'PUBLIC-PROBES.lean.txt']:
    assert not (WORK / name).exists(), name
(WORK / 'SOURCES-NORMAL-STAGING.json').write_text(json.dumps(stage, indent=2) + '\n')
(WORK / 'IMPORTS.lean.txt').write_bytes(imports)
(WORK / 'PUBLIC-PROBES.lean.txt').write_bytes(probes)
for item in components:
    (ROOT / item['source_path']).write_bytes((BASE / item['packet'] / item['source']).read_bytes())
(ROOT / 'lean/MicroCFTA/Audit.lean').write_bytes(imports + old_audit + b'\n' + probes)
assert len(list((ROOT / 'lean/MicroCFTA').glob('*.lean'))) == 6264
assert (ROOT / 'lean/MicroCFTA/Audit.lean').read_bytes().count(b'#print axioms ') == 695
for name, digest in baseline.items():
    if name != 'lean/MicroCFTA/Audit.lean':
        assert SHA((ROOT / name).read_bytes()) == digest, name
print(json.dumps({'staged_modules': 6, 'public_reports': 5, 'private_helpers': 30,
                  'pure_prop_definitions': 3, 'old_source_exact': 6257,
                  'audit_import_offset': len(imports)}))
