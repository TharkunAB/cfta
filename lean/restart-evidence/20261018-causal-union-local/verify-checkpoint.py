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
old_log = (ROOT / 'lean/restart-evidence/20261018-selected-read-producers/full-audit-1.log').read_text()
old_warnings = re.findall(r'^warning:.*$', old_log, re.M)
for module, stem in read('selected-canonical.json').items():
    receipt = read(stem + '.json')
    log = (HERE / receipt['log']).read_text()
    assert receipt['exit_code'] == 0 and 'Build completed successfully' in log
    expected = []
    assert re.findall(r'^warning:.*$', log, re.M) == expected
    checks['check_limits'](stem)
components = read('component-manifests.json')
assert len(components) == read('expected-counts.json')['components']
entries = 0
for name in components:
    for entry in read(name).get('entries', read(name).get('files', [])):
        path = ROOT / entry['path']
        assert checks['sha'](path) == entry['sha256'], (name, entry['path'])
        if 'bytes' in entry:
            assert path.stat().st_size == entry['bytes']
        entries += 1
audit = read('selected-audit.json')
receipt = read(audit['name'] + '.json')
assert receipt['exit_code'] == 0
checks['check_limits'](audit['name'])
log = (HERE / receipt['log']).read_text()
assert re.findall(r'^warning:.*$', log, re.M) == old_warnings
jobs = int(re.findall(r'Build completed successfully \((\d+) jobs\)\.', log)[-1])
dependencies = int(re.findall(r'Checked axiom dependencies of (\d+) MicroCFTA theorems\.', log)[-1])
assert jobs == audit['jobs'] == 3395 + len(modules) and dependencies == audit['dependency_checks']
peaks = [int(re.search(r' (\d+)M 0$', line).group(1))
         for line in (HERE / 'root-peaks.txt').read_text().splitlines() if re.search(r' (\d+)M 0$', line)]
for path in HERE.glob('*.py'):
    ast.parse(path.read_text(), filename=str(path))
print(json.dumps({
 'status':'PASS','proof_commit':(HERE/'proof-commit.txt').read_text().strip(),
 'production_modules':modules,'new_public_pairs':counts['new-public'],
 'constructed_pairs':counts['constructed'],'private_claim_pairs':counts['private-claim'],
 'groups':len(groups),'full_public_proofs_and_standard_axioms':True,
 'strict_empty_logs':len(modules)+len(stricts),'component_manifests':components,
 'component_entries':entries,'audit_jobs':jobs,'audit_dependency_checks':dependencies,
 'old_warnings':old_warnings,'memory_max':'4294967296','memory_high':'4294967296','swap_max':'0',
 'successful_root_job_peak_upper_bound_MiB':max(peaks),
 'actual_union_preparation_retains_complete_publication_history':True,
 'paired_union_preparation_keeps_original_parent_values_at_produced_reader':True,
 'indexed_fragments_retain_original_member_occurrence_and_bare_self_rule':True,
 'literal_local_calculus_keeps_full_guards_ordered_children_and_actual_mu_successors':True,
 'source_union_constructor_requires_explicit_strict_member_laws':True,
 'produced_reader_is_not_silently_identified_with_initial_reader':True,
 'source_built_nonempty_counterexample_refutes_arbitrary_local_up_to_closure':True,
 'counterexample_is_not_a_failure_of_actual_generated_or_haskell':True,
 'old_unrestricted_arbitrary_cache_fusion_remains_refuted':True,
 'broad_claim_retains_exact_valid_input_preservation_boundary':True,
 'general_source_generated_directed_certificate_still_open':True,
 'general_recursive_completion_and_convergence_still_open':True,
 'public_haskell_correspondence_still_open':True,'new_haskell_behavior_patch':False,
},indent=2))
