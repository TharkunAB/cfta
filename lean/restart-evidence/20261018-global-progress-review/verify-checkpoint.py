import datetime, hashlib, json, re, runpy
from pathlib import Path
from zoneinfo import ZoneInfo
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
def read(name): return json.loads((HERE/name).read_text())
checks=runpy.run_path(str(HERE/'verify-probes.py'))
assert read('selection-status.json')['finalized']
groups=read('selected-groups.json')
assert len(groups)==4
assert sum(g['pairs'] for g in groups if g['kind']=='new-public')==11
assert sum(g['pairs'] for g in groups if g['kind']=='constructed')==2
for group in groups: checks['check_group'](group)
modules=read('frozen-modules.json')
assert len(modules)==2
for module,expected in modules.items():
 assert checks['sha'](ROOT/'lean/MicroCFTA'/f'{module}.lean')==expected
for module,stem in read('selected-strict.json').items():
 receipt=read(stem+'.json')
 assert receipt['exit_code']==0
 assert not (HERE/receipt['log']).read_bytes()
 assert checks['sha'](HERE/receipt['source'])==modules[module]
 checks['check_limits'](stem)
for module,stem in read('selected-canonical.json').items():
 receipt=read(stem+'.json')
 assert receipt['exit_code']==0
 assert 'Build completed successfully' in (HERE/receipt['log']).read_text()
 checks['check_limits'](stem)
for stem in ['native-guards-kernels-1','closed-alphabet-kernels-4']:
 receipt=read(stem+'.json')
 assert receipt['exit_code']==0 and not (HERE/receipt['log']).read_bytes()
 checks['check_limits'](stem)
components=read('component-manifests.json')
entries=0
for name in components:
 manifest=read(name)
 for entry in manifest['entries']:
  assert checks['sha'](ROOT/entry['path'])==entry['sha256'],(name,entry['path'])
  if 'bytes' in entry: assert (ROOT/entry['path']).stat().st_size==entry['bytes']
 entries+=len(manifest['entries'])
receipt=read('full-audit-1.json')
assert receipt['exit_code']==0
checks['check_limits']('full-audit-1')
log=(HERE/receipt['log']).read_text()
warnings=re.findall(r'^warning:.*$',log,re.M)
old=(ROOT/'lean/restart-evidence/20261018-parent-row-trace/full-audit-1.log').read_text()
assert warnings==re.findall(r'^warning:.*$',old,re.M)
jobs=int(re.findall(r'Build completed successfully \((\d+) jobs\)\.',log)[-1])
deps=int(re.findall(r'Checked axiom dependencies of (\d+) MicroCFTA theorems\.',log)[-1])
assert jobs==3208 and deps==70665
observed=datetime.datetime.fromisoformat(receipt['observed_at']).astimezone(ZoneInfo('Europe/Stockholm')).strftime('%Y-%m-%dT%H:%M:%S')
peaks=[int(re.search(r' (\d+)M 0$',line).group(1)) for line in (HERE/'root-peaks.txt').read_text().splitlines() if line.startswith(observed+' ')]
assert peaks
failed=read('inherited-pattern-1.json')
assert failed['exit_code']!=0 and 'Failed to connect to bus' in (HERE/failed['log']).read_text()
assert not (HERE/'inherited-pattern-1.limits.json').exists()
for stem in ['fixed-own-footprint-1','fixed-own-footprint-2']:
 assert read(stem+'.json')['exit_code']==-15
 checks['check_limits'](stem)
for stem in ['inherited-pattern-2','fixed-own-footprint-3']:
 assert read(stem+'.json')['exit_code']==0
 checks['check_limits'](stem)
print(json.dumps({'status':'PASS','proof_commit':(HERE/'proof-commit.txt').read_text().strip(),
 'production_modules':modules,'new_public_pairs':11,'constructed_pairs':2,'groups':4,
 'full_public_proofs_and_standard_axioms':True,'strict_empty_logs':4,
 'component_manifests':components,'component_entries':entries,
 'audit_jobs':jobs,'audit_dependency_checks':deps,'old_warnings':warnings,
 'memory_max':'4294967296','memory_high':'4294967296','swap_max':'0','audit_peak_MiB':max(peaks),
 'interrupted_footprint_proofs':2,'footprint_and_pattern_runs_are_diagnostics':True,
 'actual_success_preserves_causal_guard_heap_without_supplied_trace':True,
 'fixed_finite_stored_guard_carrier_without_instruction_ceiling':True,
 'fixed_carrier_requires_actual_checked_trace':True,
 'completion_still_a_native_preservation_premise':True,
 'proper_initial_row_lineage_still_open':True,'global_inherited_carrier_still_open':True,
 'all_active_key_exclusion_still_open':True,'finite_fresh_call_bound_still_open':True,
 'general_recursive_outer_completion_still_open':True,'repeated_convergence_still_open':True,
 'used_binder_and_earlier_writer_alignment_still_open':True,
 'public_haskell_correspondence_still_open':True,'new_haskell_behavior_patch':False},indent=2))
