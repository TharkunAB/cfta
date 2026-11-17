from pathlib import Path
import hashlib
import json
import re
import subprocess

ROOT = Path('/home/tritlo/Code/mcfta')
BASE = ROOT / 'lean/restart-evidence'
WORK = Path(__file__).resolve().parent
SHA = lambda data: hashlib.sha256(data).hexdigest()
receipt = json.loads((WORK / 'PRIVATE-CHECK-VERIFIED.json').read_text())
run = BASE / receipt['run']
report = json.loads((run / 'checked.json').read_text())
selection = json.loads((run / 'selection.json').read_text())
assert receipt['actual_terminal'] and receipt['actual_terminal_exit'] == 0
assert receipt['checks'] == report['checks'] and report['three_modules_checked']
assert len(report['checks']) == 3 and all(report['passed'])
assert report['actual_public_axiom_reports'] == 3
assert report['private_explicit_reports'] == report['actual_definition_declaration_checks'] == 0
assert report['private_helpers_compiled_transitively'] == 46
assert not report['joint_finite_completion_proved'] and not report['haskell_changed']
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT).decode().strip() == 'a59893a37d6c30b25a92f6ac499e5115057b9383'
assert not subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=no'], cwd=ROOT)
for name, digest in json.loads((run / 'source-pins.json').read_text()).items():
    assert SHA((ROOT / name).read_bytes()) == digest, name
baseline = json.loads((WORK / 'baseline-source-pins.json').read_text())
assert len(baseline) == 6264
for name, digest in baseline.items():
    assert SHA((ROOT / name).read_bytes()) == digest, name
old_audit = (WORK / 'Audit-BEFORE.lean.txt').read_bytes()
assert old_audit == (ROOT / 'lean/MicroCFTA/Audit.lean').read_bytes()
assert len(old_audit) == 429545 and old_audit.count(b'#print axioms ') == 695
components = []
imports = b''
probes = b''
private_count = 0
public_count = 0
carrier_count = 0
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
    carriers = re.findall(r'^private def (\w+)', raw.decode(), re.M)
    assert len(public) == item['expected_axiom_reports'] == 1
    assert len(private) == item['private_theorems']
    assert len(carriers) == item['private_prop_definitions']
    assert re.findall(r'^#print axioms (\S+)', probe.decode(), re.M) == [item['public_qname']]
    components.append(dict(item, source_path=str(target.relative_to(ROOT)), raw_bytes=len(raw),
        names=[item['public_qname']], new_private_helper_names=private, new_private_prop_names=carriers))
    private_count += len(private)
    public_count += len(public)
    carrier_count += len(carriers)
    imports += ('import MicroCFTA.' + item['module'] + '\n').encode()
    probes += probe
assert len(components) == 3 and (private_count, public_count, carrier_count) == (46, 3, 4)
assert imports.count(b'import ') == 3 and probes.count(b'#print axioms ') == 3
assert probes.count(b'#check ') == 0
stage = {'prior_checkpoint': 'a59893a37d6c30b25a92f6ac499e5115057b9383',
    'source_baseline': selection['source_commit'], 'private_run': receipt['run'],
    'private_success_session': receipt['actual_session'], 'components': components,
    'baseline_overrides': {'lean/MicroCFTA/Audit.lean': str((WORK / 'Audit-BEFORE.lean.txt').relative_to(ROOT))},
    'source_files': 6267, 'audit_imports': 5267, 'audit_reports': 698,
    'independent_reports': 293, 'new_modules': 3, 'changed_existing_owners': 0,
    'new_public_theorems': 3, 'new_private_helpers': 46, 'new_theorem_declarations': 49,
    'new_private_predicates': 4, 'new_prop_definitions': 4, 'new_definition_declaration_checks': 0,
    'fresh_reports': 3, 'inherited_reports': 489, 'combined_reports': 492,
    'old_source_files_byte_exact': 6263, 'old_audit_bytes': len(old_audit),
    'old_audit_sha256': SHA(old_audit), 'old_audit_exact_offset': len(imports),
    'new_audit_imports': 3, 'all_three_original_first_headers_exact': True,
    'all_old_proof_bodies_and_limits_unchanged': True,
    'first_check_failed_missing_checked_alias': True, 'checked_alias_only_repair': True,
    'all_new_formal_proof_checks_first_pass': False,
    'actual_next_warm_mu_owner_admission_proved': True,
    'actual_next_warm_optional_prefix_no_new_mu_proved': True,
    'next_warm_after_one_cold_prefix_no_new_mu_proved': True,
    'whole_next_warm_execute_outcome_and_all_prefixes_no_new_mu_proved': True,
    'warm_query_no_new_mu_proved': True,
    'warm_no_new_mu_scope': {'old': 'one actual bounded cold prefix, with any oldControl',
        'new': 'literal emptyDomain root with closed Available operands and original InputsThrough/FieldsThrough',
        'result': 'actual execute outcome heap and every bounded Trace prefix preserve complete Mu inventory',
        'not_covered': 'arbitrary independent warm-query sequences, semantic inhabitance, joint finite completion or Haskell correspondence'},
    'arbitrary_independent_warm_query_sequence_proved': False,
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
assert len(list((ROOT / 'lean/MicroCFTA').glob('*.lean'))) == 6267
assert (ROOT / 'lean/MicroCFTA/Audit.lean').read_bytes().count(b'#print axioms ') == 698
for name, digest in baseline.items():
    if name != 'lean/MicroCFTA/Audit.lean':
        assert SHA((ROOT / name).read_bytes()) == digest, name
print(json.dumps({'staged_modules': 3, 'public_reports': 3, 'private_helpers': 46,
    'private_prop_carriers': 4, 'old_source_exact': 6263, 'audit_import_offset': len(imports)}))
