import datetime,json,re,runpy
from pathlib import Path
from zoneinfo import ZoneInfo
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[2]
def read(n):return json.loads((HERE/n).read_text())
c=runpy.run_path(str(HERE/'verify-probes.py'))
assert read('selection-status.json')['finalized']
groups=read('selected-groups.json')
public=sum(g['pairs'] for g in groups if g['kind']=='new-public')
constructed=sum(g['pairs'] for g in groups if g['kind']=='constructed')
assert public==11
for g in groups:c['check_group'](g)
modules=read('frozen-modules.json');assert len(modules)==5
for module,expected in modules.items():assert c['sha'](ROOT/'lean/MicroCFTA'/f'{module}.lean')==expected
for module,stem in read('selected-strict.json').items():
 receipt=read(stem+'.json');assert receipt['exit_code']==0 and not (HERE/receipt['log']).read_bytes()
 assert c['sha'](HERE/receipt['source'])==modules[module];c['check_limits'](stem)
for module,stem in read('selected-canonical.json').items():
 receipt=read(stem+'.json');assert receipt['exit_code']==0
 assert 'Build completed successfully' in (HERE/receipt['log']).read_text();c['check_limits'](stem)
stricts=read('selected-constructed-strict.json');assert len(stricts)==5
for stem in stricts:
 receipt=read(stem+'.json');assert receipt['exit_code']==0 and not (HERE/receipt['log']).read_bytes();c['check_limits'](stem)
components=read('component-manifests.json');assert len(components)==7
entries=0
for name in components:
 for entry in read(name)['entries']:
  path=ROOT/entry['path'];assert c['sha'](path)==entry['sha256'],(name,entry['path'])
  if 'bytes' in entry:assert path.stat().st_size==entry['bytes']
  entries+=1
receipt=read('full-audit-1.json');assert receipt['exit_code']==0;c['check_limits']('full-audit-1')
log=(HERE/receipt['log']).read_text();warnings=re.findall(r'^warning:.*$',log,re.M)
old=(ROOT/'lean/restart-evidence/20261018-actual-positional-lineage/full-audit-3.log').read_text()
assert warnings==re.findall(r'^warning:.*$',old,re.M)
jobs=int(re.findall(r'Build completed successfully \((\d+) jobs\)\.',log)[-1])
deps=int(re.findall(r'Checked axiom dependencies of (\d+) MicroCFTA theorems\.',log)[-1])
assert jobs==3221 and deps==70817
observed=datetime.datetime.fromisoformat(receipt['observed_at']).astimezone(ZoneInfo('Europe/Stockholm')).strftime('%Y-%m-%dT%H:%M:%S')
peaks=[int(re.search(r' (\d+)M 0$',line).group(1)) for line in (HERE/'root-peaks.txt').read_text().splitlines() if line.startswith(observed+' ')];assert peaks
print(json.dumps({'status':'PASS','proof_commit':(HERE/'proof-commit.txt').read_text().strip(),
 'production_modules':modules,'new_public_pairs':public,'constructed_pairs':constructed,'groups':len(groups),
 'full_public_proofs_and_standard_axioms':True,'strict_empty_logs':len(modules)+len(stricts),
 'component_manifests':components,'component_entries':entries,'audit_jobs':jobs,'audit_dependency_checks':deps,
 'old_warnings':warnings,'memory_max':'4294967296','memory_high':'4294967296','swap_max':'0','audit_peak_MiB':max(peaks),
 'actual_scan_supplies_selected_original_roots_without_heap_or_memo_laws':True,
 'raw_signed_paths_derive_required_compiler_absence':True,
 'canonical_selected_record_paths_derive_required_compiler_absence':True,
 'untouched_class_fold_retains_literal_values_without_root':True,
 'actual_local_classes_no_supplied_root_or_compiled_absence':True,
 'actual_precheck_and_reduce_derive_origins_from_initial_raw_constraint_footprint':True,
 'positive_continuation_has_strict_mass_below_immediate_anchor':True,
 'initial_raw_footprint_and_successful_worker_equations_remain_explicit':True,
 'generated_anchor_need_not_be_an_initial_source_occurrence':True,
 'proper_initial_row_lineage_still_open':True,'global_inherited_carrier_still_open':True,
 'all_active_key_exclusion_still_open':True,'finite_fresh_call_bound_still_open':True,
 'general_recursive_outer_completion_still_open':True,'repeated_convergence_still_open':True,
 'used_binder_and_earlier_writer_alignment_still_open':True,'public_haskell_correspondence_still_open':True,
 'new_haskell_behavior_patch':False},indent=2))
