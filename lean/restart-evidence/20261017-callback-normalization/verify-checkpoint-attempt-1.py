import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def limits(stem):
    path = HERE / (stem + '.limits.json')
    if path.exists():
        observed = json.loads(path.read_text())
        assert observed['memory.max'] == observed['memory.high'] == '4294967296', observed
        assert observed['memory.swap.max'] == '0', observed
    else:
        assert (HERE / (stem + '.caps')).read_text().split() == ['4294967296', '4294967296', '0']

groups = json.loads((HERE / 'selected-groups.json').read_text())
for group in groups:
    stem, count = group['name'], group['pairs']
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert meta['exit_code'] == 0, (stem, meta)
    source = (HERE / meta['source']).read_text()
    log = (HERE / meta['log']).read_text()
    for option in ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true', 'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']:
        assert 'set_option ' + option in source, (stem, option)
    assert len(re.findall(r'^#check @', source, re.M)) == count, stem
    assert len(re.findall(r'^#print axioms ', source, re.M)) == count, stem
    if group['full_proof']:
        assert len(re.findall(r'^#print (?!axioms )', source, re.M)) == count, stem
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|⋯|…|\.\.\.', log), stem
    reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
    no_axioms = len(re.findall(r'does not depend on any axioms', log))
    assert len(reports) + no_axioms == count, (stem, len(reports), no_axioms)
    for report in reports:
        cleaned = re.sub(r'\.\{[^}]*\}', '', report)
        names = set(re.split(r',\s*', cleaned.strip()))
        assert names <= {'propext', 'Classical.choice', 'Quot.sound'}, (stem, names)
    limits(stem)

modules = json.loads((HERE / 'frozen-modules.json').read_text())
for module, expected in modules.items():
    assert sha(ROOT / 'lean/MicroCFTA' / (module + '.lean')) == expected, module

stricts = json.loads((HERE / 'selected-strict.json').read_text())
for module, stem in stricts.items():
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert meta['exit_code'] == 0, stem
    assert not (HERE / meta['log']).read_bytes(), stem
    assert sha(HERE / meta['source']) == modules[module], (stem, module)
    limits(stem)

audit = json.loads((HERE / 'full-audit-1.json').read_text())
assert audit['exit_code'] == 0
limits('full-audit-1')
log = (HERE / audit['log']).read_text()
audit_jobs = int(re.findall(r'Build completed successfully \((\d+) jobs\)\.', log)[-1])
audit_dependencies = int(re.findall(r'Checked axiom dependencies of (\d+) MicroCFTA theorems\.', log)[-1])
audit_peak = int(re.findall(r' (\d+)M 0$', (HERE / 'root-peaks.txt').read_text(), re.M)[-1])

components = json.loads((HERE / 'component-manifests.json').read_text())
entries = 0
for name in components:
    content = json.loads((HERE / name).read_text())
    for entry in content['entries']:
        path = ROOT / entry['path']
        assert sha(path) == entry['sha256'], (name, entry['path'])
    entries += len(content['entries'])

report = {'status': 'PASS', 'proof_commit': (HERE / 'proof-commit.txt').read_text().strip(),
    'new_public_pairs': sum(g['pairs'] for g in groups if g['kind'] == 'new-public'),
    'existing_status_pairs': sum(g['pairs'] for g in groups if g['kind'] == 'status'),
    'constructed_pairs': sum(g['pairs'] for g in groups if g['kind'] == 'constructed'),
    'all_pairs': sum(g['pairs'] for g in groups), 'groups': groups,
    'production_modules': modules, 'strict_sources': stricts,
    'component_manifests': components, 'component_entries': entries,
    'audit_jobs': audit_jobs, 'audit_dependency_checks': audit_dependencies, 'audit_peak_MiB': audit_peak,
    'memory_max': '4294967296', 'memory_high': '4294967296', 'swap_max': '0',
    'only_standard_axioms': True, 'complete_proof_output': True,
    'general_recursive_warm_provenance_still_open': True,
    'general_outer_progress_still_open': True, 'new_haskell_behavior_patch': False}
print(json.dumps(report, indent=2))
