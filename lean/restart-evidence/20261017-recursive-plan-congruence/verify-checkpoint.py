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

audit = json.loads((HERE / 'full-audit-1.json').read_text())
assert audit['exit_code'] == 0
check_limits('full-audit-1')
log = (HERE / audit['log']).read_text()
jobs = int(re.findall(r'Build completed successfully \((\d+) jobs\)\.', log)[-1])
dependencies = int(re.findall(r'Checked axiom dependencies of (\d+) MicroCFTA theorems\.', log)[-1])
observed = datetime.datetime.fromisoformat(audit['observed_at']).astimezone(ZoneInfo('Europe/Stockholm')).strftime('%Y-%m-%dT%H:%M:%S')
peak_line = next(line for line in (HERE / 'root-peaks.txt').read_text().splitlines() if line.startswith(observed + ' '))
peak = int(re.search(r' (\d+)M 0$', peak_line).group(1))

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
    'audit_jobs': jobs,
    'audit_dependency_checks': dependencies,
    'audit_peak_MiB': peak,
    'memory_max': '4294967296',
    'memory_high': '4294967296',
    'swap_max': '0',
    'only_standard_axioms': True,
    'complete_proof_output': True,
    'general_outer_progress_still_open': True,
    'new_haskell_behavior_patch': False,
}
print(json.dumps(report, indent=2))
