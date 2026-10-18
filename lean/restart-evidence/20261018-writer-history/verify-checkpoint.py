import ast
import json
import re
import runpy
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def read(name):
    return json.loads((HERE / name).read_text())


checks = runpy.run_path(str(HERE / 'verify-probes.py'))
assert read('selection-status.json')['finalized']
groups = read('selected-groups.json')
assert len({group['name'] for group in groups}) == len(groups)
counts = {kind: sum(group['pairs'] for group in groups if group['kind'] == kind)
          for kind in ['new-public', 'constructed', 'private-claim']}
assert counts == read('expected-counts.json')['pairs']
for group in groups:
    checks['check_group'](group)
modules = read('frozen-modules.json')
assert len(modules) == read('expected-counts.json')['modules']
for module, expected in modules.items():
    assert checks['sha'](ROOT / 'lean/MicroCFTA' / (module + '.lean')) == expected
for module, stem in read('selected-strict.json').items():
    receipt = read(stem + '.json')
    assert receipt['exit_code'] == 0 and not (HERE / receipt['log']).read_bytes()
    assert checks['sha'](HERE / receipt['source']) == modules[module]
    checks['check_limits'](stem)
stricts = read('selected-constructed-strict.json')
assert len(stricts) == read('expected-counts.json')['constructed_strict']
for stem, working in stricts.items():
    receipt = read(stem + '.json')
    assert receipt['exit_code'] == 0 and not (HERE / receipt['log']).read_bytes()
    assert checks['sha'](HERE / receipt['source']) == receipt['sha256']
    assert checks['sha'](HERE / receipt['source']) == checks['sha'](HERE / working)
    checks['check_limits'](stem)
old_log = (ROOT / 'lean/restart-evidence/20261018-outer-owner-progress/full-audit-1.log').read_text()
old_warnings = re.findall(r'^warning:.*$', old_log, re.M)
assert len(old_warnings) == 1
for module, stem in read('selected-canonical.json').items():
    receipt = read(stem + '.json')
    log = (HERE / receipt['log']).read_text()
    assert receipt['exit_code'] == 0 and 'Build completed successfully' in log
    assert re.findall(r'^warning:.*$', log, re.M) == old_warnings
    checks['check_limits'](stem)
component_entries = 0
components = read('component-manifests.json')
assert len(components) == read('expected-counts.json')['components']
for name in components:
    for entry in read(name).get('entries', read(name).get('files', [])):
        path = ROOT / entry['path']
        assert checks['sha'](path) == entry['sha256'], (name, entry['path'])
        if 'bytes' in entry:
            assert path.stat().st_size == entry['bytes']
        component_entries += 1
pins = read('progress-review-source-pins.json')['files']
for entry in pins:
    path = ROOT / entry['path']
    assert checks['sha'](path) == entry['sha256'], entry['path']
    assert path.stat().st_size == entry['bytes']
audit = read('selected-audit.json')
receipt = read(audit['name'] + '.json')
assert receipt['exit_code'] == 0
checks['check_limits'](audit['name'])
log = (HERE / receipt['log']).read_text()
assert re.findall(r'^warning:.*$', log, re.M) == old_warnings
jobs = int(re.findall(r'Build completed successfully \((\d+) jobs\)\.', log)[-1])
dependencies = int(re.findall(r'Checked axiom dependencies of (\d+) MicroCFTA theorems\.', log)[-1])
assert jobs == audit['jobs'] == 3421 + len(modules)
assert dependencies == audit['dependency_checks'] == read('expected-counts.json')['audit_dependency_checks']
for path in HERE.glob('*.py'):
    ast.parse(path.read_text(), filename=str(path))
print(json.dumps({
    'status': 'PASS', 'proof_commit': (HERE / 'proof-commit.txt').read_text().strip(),
    'production_modules': modules, 'new_public_pairs': counts['new-public'],
    'constructed_pairs': counts['constructed'], 'groups': len(groups),
    'full_public_proofs_and_standard_axioms': True,
    'strict_empty_logs': len(modules) + len(stricts),
    'component_manifests': components, 'component_entries': component_entries,
    'progress_review_source_pins': len(pins),
    'audit_jobs': jobs, 'audit_dependency_checks': dependencies, 'old_warnings': old_warnings,
    'memory_max': '4294967296', 'memory_high': '4294967296', 'swap_max': '0',
    'literal_target_edit_class_parent_calls_preserve_actual_merge_writers': True,
    'outer_returns_and_unfinished_phase_prefixes_preserve_actual_merge_writers': True,
    'logical_empty_initial_merge_derives_raw_history': True,
    'initial_physical_good_probe_and_request_readiness_remain_explicit': True,
    'arbitrary_initial_warm_tables_require_raw_history': True,
    'all_terminal_lower_failure_states_not_claimed': True,
    'strict_source_renewal_progress_still_open': True,
    'broad_constructed_root_and_exact_query_claims_unchanged': True,
    'general_completion_convergence_and_haskell_refinement_still_open': True,
    'new_haskell_behavior_patch': False,
}, indent=2))
