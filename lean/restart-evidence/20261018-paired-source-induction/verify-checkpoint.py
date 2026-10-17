import datetime
import json
import re
import runpy
from pathlib import Path
from zoneinfo import ZoneInfo

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
selection = json.loads((HERE / 'selection-status.json').read_text())
assert selection['finalized'], 'Checkpoint selections remain PARTIAL'
checks = runpy.run_path(str(HERE / 'verify-probes.py'))
sha, check_limits, check_group = (checks[name] for name in ['sha', 'check_limits', 'check_group'])

groups = json.loads((HERE / 'selected-groups.json').read_text())
assert len({group['name'] for group in groups}) == len(groups)
for group in groups:
    check_group(group)

modules = json.loads((HERE / 'frozen-modules.json').read_text())
for name, expected in modules.items():
    assert sha(ROOT / 'lean/MicroCFTA' / (name + '.lean')) == expected, name

stricts = json.loads((HERE / 'selected-strict.json').read_text())
assert set(stricts) == set(modules)
for name, stem in stricts.items():
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert meta['exit_code'] == 0, stem
    assert not (HERE / meta['log']).read_bytes(), stem
    assert sha(HERE / meta['source']) == modules[name], (name, stem)
    check_limits(stem)

canonicals = json.loads((HERE / 'selected-canonical.json').read_text())
assert set(canonicals) == set(modules)
for name, stem in canonicals.items():
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert meta.get('exit_code', meta.get('exit')) == 0, (name, stem)
    assert 'Build completed successfully' in (HERE / meta.get('log', stem + '.log')).read_text(), stem
    check_limits(stem)

components = json.loads((HERE / 'component-manifests.json').read_text())
component_entries = 0
for name in components:
    manifest = json.loads((HERE / name).read_text())
    entries = manifest.get('entries', manifest.get('files'))
    assert isinstance(entries, list), name
    for entry in entries:
        assert sha(ROOT / entry['path']) == entry['sha256'], (name, entry['path'])
    component_entries += len(entries)

audit_stem = json.loads((HERE / 'selected-audit.json').read_text())['name']
audit = json.loads((HERE / (audit_stem + '.json')).read_text())
assert audit['exit_code'] == 0
check_limits(audit_stem)
log = (HERE / audit['log']).read_text()
jobs = int(re.findall(r'Build completed successfully \((\d+) jobs\)\.', log)[-1])
warnings = re.findall(r'^warning:.*$', log, re.M)
previous_warnings = re.findall(r'^warning:.*$', (ROOT / 'lean/restart-evidence/20261018-native-node-lineage/full-audit-1.log').read_text(), re.M)
assert warnings == previous_warnings
dependencies = int(re.findall(r'Checked axiom dependencies of (\d+) MicroCFTA theorems\.', log)[-1])
observed = datetime.datetime.fromisoformat(audit['observed_at']).astimezone(ZoneInfo('Europe/Stockholm')).strftime('%Y-%m-%dT%H:%M:%S')
peak_lines = [line for line in (HERE / 'root-peaks.txt').read_text().splitlines() if line.startswith(observed + ' ')]
peaks = [int(re.search(r' (\d+)M 0$', line).group(1)) for line in peak_lines]
peak = max(peaks)

report = {
    'status': 'PASS',
    'proof_commit': (HERE / 'proof-commit.txt').read_text().strip(),
    'new_public_pairs': sum(group['pairs'] for group in groups if group['kind'] == 'new-public'),
    'constructed_pairs': sum(group['pairs'] for group in groups if group['kind'] == 'constructed'),
    'all_pairs': sum(group['pairs'] for group in groups),
    'groups': groups,
    'production_modules': modules,
    'strict_sources': stricts,
    'canonical_targets': canonicals,
    'component_manifests': components,
    'component_entries': component_entries,
    'audit_receipt': audit_stem,
    'replayed_existing_warnings': warnings,
    'audit_jobs': jobs,
    'audit_dependency_checks': dependencies,
    'audit_peak_MiB': peak,
    'audit_peak_is_upper_bound': len(peaks) > 1,
    'same_second_scope_peaks_MiB': peaks,
    'memory_max': '4294967296',
    'memory_high': '4294967296',
    'swap_max': '0',
    'only_standard_axioms': True,
    'new_public_complete_proof_output': all(g['full_proof'] for g in groups if g['kind'] == 'new-public'),
    'constructed_full_proof_pairs': sum(g['pairs'] for g in groups if g['kind'] == 'constructed' and g['full_proof']),
    'constructed_axiom_only_pairs': sum(g['pairs'] for g in groups if g['kind'] == 'constructed' and not g['full_proof']),
    'general_outer_progress_still_open': True,
    'all_active_node_key_exclusion_still_open': True,
    'retained_mu_binder_and_warm_writer_alignment_still_open': True,
    'paired_ordinary_induction_step_checked': True,
    'selected_native_cell_retained_at_full_reader': True,
    'actual_suffix_derives_full_reader_history': True,
    'new_haskell_behavior_patch': False,
    'binder_result_and_union_source_cases_still_open': True,
    'support_compatibility_execution_congruence_still_open': True,
}
print(json.dumps(report, indent=2))
