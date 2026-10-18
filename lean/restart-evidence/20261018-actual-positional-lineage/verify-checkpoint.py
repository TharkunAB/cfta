import datetime,json,re,runpy
from pathlib import Path
from zoneinfo import ZoneInfo
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[2]
def read(name):return json.loads((HERE/name).read_text())
checks=runpy.run_path(str(HERE/'verify-probes.py'))
assert read('selection-status.json')['finalized']
groups=read('selected-groups.json')
assert len(groups)==12 and sum(g['pairs'] for g in groups if g['kind']=='new-public')==31
assert sum(g['pairs'] for g in groups if g['kind']=='constructed')==6
for g in groups:checks['check_group'](g)
modules=read('frozen-modules.json');assert len(modules)==6
for module,expected in modules.items():assert checks['sha'](ROOT/'lean/MicroCFTA'/f'{module}.lean')==expected
for module,stem in read('selected-strict.json').items():
 receipt=read(stem+'.json')
 assert receipt['exit_code']==0 and not (HERE/receipt['log']).read_bytes()
 assert checks['sha'](HERE/receipt['source'])==modules[module]
 checks['check_limits'](stem)
for module,stem in read('selected-canonical.json').items():
 receipt=read(stem+'.json')
 assert receipt['exit_code']==0 and 'Build completed successfully' in (HERE/receipt['log']).read_text()
 checks['check_limits'](stem)
for stem in read('selected-constructed-strict.json'):
 receipt=read(stem+'.json')
 assert receipt['exit_code']==0 and not (HERE/receipt['log']).read_bytes()
 checks['check_limits'](stem)
components=read('component-manifests.json');entries=0
for name in components:
 manifest=read(name)
 for entry in manifest['entries']:
  assert checks['sha'](ROOT/entry['path'])==entry['sha256'],(name,entry['path'])
  if 'bytes' in entry:assert (ROOT/entry['path']).stat().st_size==entry['bytes']
 entries+=len(manifest['entries'])
receipt=read('full-audit-3.json');assert receipt['exit_code']==0;checks['check_limits']('full-audit-3')
log=(HERE/receipt['log']).read_text();warnings=re.findall(r'^warning:.*$',log,re.M)
old=(ROOT/'lean/restart-evidence/20261018-outer-guard-transport/full-audit-1.log').read_text()
assert warnings==re.findall(r'^warning:.*$',old,re.M)
jobs=int(re.findall(r'Build completed successfully \((\d+) jobs\)\.',log)[-1])
deps=int(re.findall(r'Checked axiom dependencies of (\d+) MicroCFTA theorems\.',log)[-1])
assert jobs==3216 and deps==70791
observed=datetime.datetime.fromisoformat(receipt['observed_at']).astimezone(ZoneInfo('Europe/Stockholm')).strftime('%Y-%m-%dT%H:%M:%S')
peaks=[int(re.search(r' (\d+)M 0$',line).group(1)) for line in (HERE/'root-peaks.txt').read_text().splitlines() if line.startswith(observed+' ')];assert peaks
print(json.dumps({'status':'PASS','proof_commit':(HERE/'proof-commit.txt').read_text().strip(),
 'production_modules':modules,'new_public_pairs':31,'constructed_pairs':6,'groups':12,
 'full_public_proofs_and_standard_axioms':True,'strict_empty_logs':12,
 'component_manifests':components,'component_entries':entries,
 'audit_jobs':jobs,'audit_dependency_checks':deps,'old_warnings':warnings,
 'memory_max':'4294967296','memory_high':'4294967296','swap_max':'0','audit_peak_MiB':max(peaks),
 'actual_edit_positional_origins_without_semantic_reads':True,
 'actual_false_primary_derives_selected_original_root':True,
 'primary_result_does_not_construct_execution_or_certify_edited_values':True,
 'actual_plain_head_zero_own_rows_in_mixed_heap':True,
 'actual_required_same_index_origins_from_entry_facts':True,
 'actual_class_right_fold_and_empty_propagation_positional_origins':True,
 'actual_required_then_class_pass_composes':True,
 'nonempty_own_row_retains_exact_original_continuation':True,
 'recursive_root_gate_and_compiler_footprints_remain_explicit':True,
 'immediate_forest_origin_is_not_general_initial_source_descent':True,
 'proper_initial_row_lineage_still_open':True,'global_inherited_carrier_still_open':True,
 'all_active_key_exclusion_still_open':True,'finite_fresh_call_bound_still_open':True,
 'general_recursive_outer_completion_still_open':True,'repeated_convergence_still_open':True,
 'used_binder_and_earlier_writer_alignment_still_open':True,
 'public_haskell_correspondence_still_open':True,'new_haskell_behavior_patch':False},indent=2))
