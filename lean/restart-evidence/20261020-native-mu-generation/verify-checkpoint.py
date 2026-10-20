import ast
import hashlib
import json
import re
import runpy
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def manifest_entries(manifest):
    for key in ['entries', 'files', 'pins']:
        if key in manifest:
            assert isinstance(manifest[key], list)
            return manifest[key]
    raise AssertionError('Manifest has no file entries')


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
read_proof = (HERE / 'proof-commit.txt').read_text().strip()
assert subprocess.run(['git', 'merge-base', '--is-ancestor', read_proof, 'HEAD'], cwd=ROOT).returncode == 0
modules = read('frozen-modules.json')
assert len(modules) == read('expected-counts.json')['modules']
assert set(read('selected-strict.json')) == set(modules)
assert set(read('selected-canonical.json')) == set(modules)
heads = []
for module in modules:
    source = (ROOT / 'lean/MicroCFTA' / (module + '.lean')).read_text()
    heads += ['MicroCFTA.' + module + '.' + name for name in
              re.findall(r'^(?:theorem|def|structure|inductive) ([A-Za-z0-9_.]+)', source, re.M)]
checked_heads = []
for group in groups:
    if group['kind'] == 'new-public':
        meta = read(group['name'] + '.json')
        checked_heads += re.findall(r'^#check @([^\s]+)', (HERE / meta['source']).read_text(), re.M)
assert heads == read('public-heads.json')
assert len(heads) == len(checked_heads) == counts['new-public'] and set(heads) == set(checked_heads)
for module, expected in modules.items():
    assert checks['sha'](ROOT / 'lean/MicroCFTA' / (module + '.lean')) == expected
    committed = subprocess.check_output(['git', 'show', read_proof + ':lean/MicroCFTA/' + module + '.lean'], cwd=ROOT)
    assert hashlib.sha256(committed).hexdigest() == expected, module
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
old_log = (ROOT / 'lean/restart-evidence/20261019-head-issued-paths/full-audit-1.log').read_text()
old_warnings = re.findall(r'^warning:.*$', old_log, re.M)
assert len(old_warnings) == 1
for module, stem in read('selected-canonical.json').items():
    receipt = read(stem + '.json')
    log = (HERE / receipt['log']).read_text()
    assert receipt['exit_code'] == 0 and 'Build completed successfully' in log
    expected_warnings = read('selected-canonical-warnings.json')[module]
    assert expected_warnings in [[], old_warnings]
    assert re.findall(r'^warning:.*$', log, re.M) == expected_warnings
    checks['check_limits'](stem)
component_entries = 0
components = read('component-manifests.json')
assert len(components) == read('expected-counts.json')['components']
for name in components:
    for entry in manifest_entries(read(name)):
        path = ROOT / entry['path']
        assert checks['sha'](path) == entry['sha256'], (name, entry['path'])
        assert path.stat().st_size == entry['bytes']
        component_entries += 1
reviewed = read('source-doc-ranges.json')['ranges']
for entry in reviewed:
    lines = (ROOT / entry['path']).read_text().splitlines(keepends=True)
    actual = ''.join(lines[entry['start_line'] - 1:entry['end_line']])
    assert actual == entry['text'], entry['path']
    assert hashlib.sha256(actual.encode()).hexdigest() == entry['sha256'], entry['path']
pins = read('math-review-source-pins.json')['files']
for entry in pins:
    path = ROOT / entry['path']
    assert checks['sha'](path) == entry['sha256'], entry['path']
    assert path.stat().st_size == entry['bytes']
audit = read('selected-audit.json')
receipt = read(audit['name'] + '.json')
assert receipt['command'] == ['/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake', '-d', str(ROOT / 'lean'), 'build']
assert receipt['exit_code'] == 0
checks['check_limits'](audit['name'])
log = (HERE / receipt['log']).read_text()
assert re.findall(r'^warning:.*$', log, re.M) == old_warnings
jobs = int(re.findall(r'Build completed successfully \((\d+) jobs\)\.', log)[-1])
dependencies = int(re.findall(r'Checked axiom dependencies of (\d+) MicroCFTA theorems\.', log)[-1])
assert jobs == audit['jobs'] == 3488 + len(modules)
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
    'math_review_source_pins': len(pins),
    'reviewed_current_document_ranges': len(reviewed),
    'audit_jobs': jobs, 'audit_dependency_checks': dependencies, 'old_warnings': old_warnings,
    'memory_max': '4294967296', 'memory_high': '4294967296', 'swap_max': '0',
    'actual_stopping_source_build_derives_same_rooted_selected_writer_or_exact_initial_cell': True,
    'native_trace_recovers_same_actual_optional_instruction_and_checked_prefix_suffix': True,
    'same_native_operation_derives_generated_source_build_and_rooted_writer': True,
    'pending_source_and_yielded_native_scope_remain_distinct': True,
    'native_terminal_blocked_locator_and_captured_compileMu_owner_remain_open': True,
    'original_root_ancestry_global_renewal_haskell_refinement_remain_open': True,
    'new_haskell_behavior_patch': False,
}, indent=2))
