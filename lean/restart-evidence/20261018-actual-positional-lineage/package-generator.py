import hashlib,json,subprocess
from pathlib import Path
ROOT=Path('/home/tritlo/Code/mcfta');HERE=ROOT/'lean/restart-evidence/20261018-actual-positional-lineage'
def write(name,value):(HERE/name).write_text(json.dumps(value,indent=2)+'\n')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
proof=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
(HERE/'proof-commit.txt').write_text(proof+'\n')
names=json.loads((HERE/'new-modules.json').read_text())
primary_raw=json.loads((HERE/'primary-root-final-selection.json').read_text())
assert primary_raw['public_count']==4 and primary_raw['constructed_count']==1
primary={'strict':primary_raw['selected_strict'],'canonical':primary_raw['selected_canonical'],'constructed_strict':primary_raw['constructed_strict'],'constructed_group':next(g['name'] for g in primary_raw['selected_groups'] if g['kind']=='constructed')}
write('frozen-modules.json',{n:sha(ROOT/'lean/MicroCFTA'/f'{n}.lean') for n in names})
write('selection-status.json',{'finalized':True,'status':'FINAL'})
write('raw-log-archives.json',[])
write('selected-groups.json',[{'name':n,'pairs':k,'kind':t,'full_proof':True} for n,k,t in [
 ('actual-edit-public-1',5,'new-public'),('class-footprint-public-1',3,'new-public'),
 ('plain-head-public-1',5,'new-public'),('required-origin-public-1',9,'new-public'),('class-origin-public-1',5,'new-public'),
 ('actual-edit-kernels-public-1',1,'constructed'),('class-footprint-kernels-public-1',1,'constructed'),
 ('plain-head-kernels-public-1',1,'constructed'),('required-origin-kernels-public-1',1,'constructed'),('class-origin-kernels-public-1',1,'constructed'),('primary-root-public-1',4,'new-public'),(primary['constructed_group'],1,'constructed')]])
write('selected-strict.json',dict(zip(names,['actual-edit-direct-4','class-footprint-direct-4','plain-head-direct-2','required-origin-direct-5','class-origin-direct-4',primary['strict']])))
write('selected-canonical.json',dict(zip(names,['actual-edit-canonical-2','class-footprint-canonical-1','plain-head-canonical-1','required-origin-canonical-1','class-origin-canonical-1',primary['canonical']])))
# The final combined fixture name is supplied only after its own terminal verification.
assert (HERE/'class-origin-kernels-selection.json').exists()
kernels=json.loads((HERE/'class-origin-kernels-selection.json').read_text())
write('selected-constructed-strict.json',['actual-edit-kernels-2','class-footprint-kernels-4','plain-head-kernels-2','required-origin-kernels-3',kernels['strict'],primary['constructed_strict']])
write('selected-audit.json',{'name':'full-audit-3','jobs':3216,'dependency_checks':70791})
write('upstream-refresh.json',{'command':['git','pull','--ff-only'],'exit_code':0,'stdout':'Already up to date.\n','recorded_from_completed_call':True,'starting_head':(HERE/'starting-head.txt').read_text().strip(),'publication':'Pending direct approval. No push attempted.'})
write('component-manifests.json',['actual-edit-manifest.json','class-footprint-manifest.json','plain-head-manifest.json','required-origin-kernels-manifest.json','class-origin-kernels-manifest.json','root-support-manifest.json','primary-root-final-manifest.json','root-scope-manifest.json'])
(HERE/'verify-checkpoint.py').write_text('''import datetime,json,re,runpy
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
jobs=int(re.findall(r'Build completed successfully \\((\\d+) jobs\\)\\.',log)[-1])
deps=int(re.findall(r'Checked axiom dependencies of (\\d+) MicroCFTA theorems\\.',log)[-1])
assert jobs==3216 and deps==70791
observed=datetime.datetime.fromisoformat(receipt['observed_at']).astimezone(ZoneInfo('Europe/Stockholm')).strftime('%Y-%m-%dT%H:%M:%S')
peaks=[int(re.search(r' (\\d+)M 0$',line).group(1)) for line in (HERE/'root-peaks.txt').read_text().splitlines() if line.startswith(observed+' ')];assert peaks
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
''')
paths=[HERE/n for n in ['root-scope-review.md','root-peaks.txt','root-run-check.py','root-capped-worker.py','verify-probes.py','verify-checkpoint.py']]
for p in HERE.iterdir():
 if p.is_file() and (p.name.startswith('required-origin-') or p.name.startswith('class-origin-') or p.name.startswith('full-audit-')):paths.append(p)
for n in names+['SourceCurrentLowerOperationInvariants','SourceCurrentLowerGuardHeapReturns','SourceCurrentRequiredGuardOrigins','SourceCurrentPositionalRowOrigins','SourceCurrentRequiredHeapEffects','SourceCurrentRequiredGuard']:
 paths.append(ROOT/'lean/MicroCFTA'/f'{n}.lean')
write('root-scope-manifest.json',{'component':'root-scope-review','entries':[{'path':str(p.relative_to(ROOT)),'bytes':p.stat().st_size,'sha256':sha(p)} for p in sorted(set(paths))]})
print(json.dumps({'proof_commit':proof,'root_scope_entries':len(set(paths))}))
