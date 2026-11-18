from pathlib import Path
import ast
import json
import tempfile

ROOT = Path('/home/tritlo/Code/mcfta')
BASE = ROOT/'lean/restart-evidence'
CONTROL = BASE/'20261118-worker-endpoint-seeds-step-publication-control-draft'
STAGE_CONTROL = BASE/'20261118-worker-endpoint-seeds-step-staging-control-draft'
WORK = BASE/'20261118-worker-endpoint-seeds-step-work'
RUNTIME = BASE/'20261118-worker-endpoint-seeds-step-publication'
assert (CONTROL/'STATUS.txt').read_text().startswith('FROZEN'), 'OPEN control; do not execute.'
assert Path(__file__).resolve().parent == WORK.resolve()
assert Path(__file__).read_bytes() == (CONTROL/'prepare-publication.py').read_bytes()
assert not RUNTIME.exists(), 'Preserve every previous runtime.'
stage_bytes = (WORK/'SOURCES-NORMAL-STAGING.json').read_bytes()
assert stage_bytes == (CONTROL/'EXPECTED-STAGE.json').read_bytes()
stage = json.loads(stage_bytes)
assert stage['status'] == 'SOURCE_NORMAL_STAGING_COMPLETED' and stage['normal_Source_changed'] and not stage['published']
OVERRIDES = stage['baseline_overrides']
assert len(OVERRIDES) == 4 and 'lean/MicroCFTA/Audit.lean' in OVERRIDES
exec(compile((CONTROL/'validate-inputs.py.txt').read_text(),str(CONTROL/'validate-inputs.py.txt'),'exec'))
stage,baseline,components,raw_sources,probes,public,verified,actual,prior,classification = preflight(CONTROL)
packet(STAGE_CONTROL,read(CONTROL/'STAGING-BINDING.json')['control_manifest_sha256'])
stage_actual = read(WORK/'STAGING-ACTUAL-RUN.json')
assert stage_actual == read(CONTROL/'EXPECTED-STAGING-ACTUAL-RUN.json')
assert stage_actual['actual_terminal'] and stage_actual['actual_terminal_exit'] == 0
assert stage_actual['control_manifest_sha256'] == SHA((STAGE_CONTROL/'MANIFEST.json').read_bytes())
assert stage_actual['script_sha256'] == SHA((STAGE_CONTROL/'stage-normal-sources.py').read_bytes())
assert stage_actual['exact_Source_write_paths'] == stage['exact_Source_write_paths'] and stage_actual['git_index_empty']
assert stage_actual['normal_source_pins_sha256'] == stage['normal_source_pins_sha256']
assert stage['fresh_classification'] == classification and stage['actual_private_session'] == verified['actual_session']
normal_pins = pin_map(WORK/'NORMAL-SOURCE-PINS.json',stage['normal_source_pins_sha256'],6290)
replacements = {c['source_path']:raw_sources[c['module']] for c in components}
old_audit = historical('lean/MicroCFTA/Audit.lean',baseline['sources']['lean/MicroCFTA/Audit.lean'])
replacements['lean/MicroCFTA/Audit.lean'] = old_audit+b'\n'+public
assert set(replacements) == set(OVERRIDES)
for name,data in replacements.items():
    assert (ROOT/name).read_bytes() == data and normal_pins[name] == SHA(data)
for name,record in {**baseline['sources'],**baseline['toolchain']}.items():
    assert normal_pins[name] == (SHA(replacements[name]) if name in replacements else record['sha256'])
assert len(set(baseline['sources'])-set(replacements)) == 6282
new_audit = replacements['lean/MicroCFTA/Audit.lean']
assert len(new_audit) == 436889 and new_audit[:436723] == old_audit
assert new_audit.count(b'#print axioms ') == 746 and len(re.findall(rb'^import ',new_audit,re.M)) == 5286
prior_independent = verify(PRIOR_RUN/'IndependentProbes.lean',read(CONTROL/'PRIOR-INDEPENDENT.json')['sha256'])
assert prior_independent.count(b'#print axioms ') == 339 and prior_independent.count(b'#check ') == 300
assert all(q.encode() not in prior_independent for c in components for q in c['public_qnames']+c['private_qnames'])
public_imports = b''.join(('import MicroCFTA.'+c['module']+'\n').encode() for c in components if c['report_kind'] == 'public')
independent = public_imports+prior_independent+b'\n'+public
assert independent.count(b'#print axioms ') == 341 and independent.count(b'#check ') == 300
normal_objects = ROOT/'lean/.lake/build/lib/lean/MicroCFTA'
assert normal_objects.is_dir()
chosen = {c['module']:c for c in components}
for module in read(CONTROL/'TOPOLOGICAL-ORDER.json')['full_transitive_order']:
    if module not in chosen:
        assert (normal_objects/(module+'.olean')).is_file(),module
for name in ['shadow-compile.py.txt','strict-bind.py.txt','publication-driver.py.txt']:
    ast.parse((CONTROL/name).read_text())
bound.update([WORK/'SOURCES-NORMAL-STAGING.json',WORK/'STAGING-ACTUAL-RUN.json',WORK/'NORMAL-SOURCE-PINS.json',PRIOR_RUN/'IndependentProbes.lean'])
# Root materializes three fresh owning-module outputs. No object is copied.
RUNTIME.mkdir()
objects = Path(tempfile.mkdtemp(prefix='mcfta-worker-endpoint-seeds-step-publication-'))
(objects/'MicroCFTA').mkdir()
for obj in normal_objects.glob('*.olean'):
    if obj.stem not in chosen:
        (objects/'MicroCFTA'/obj.name).symlink_to(obj)
for module in chosen:
    assert not(objects/'MicroCFTA'/(module+'.olean')).exists()
(RUNTIME/'objects.json').write_text(json.dumps({'path':str(objects)},indent=2)+'\n')
for c in components:
    fixture = RUNTIME/'source/MicroCFTA'/c['source'];fixture.parent.mkdir(parents=True,exist_ok=True)
    fixture.write_bytes(raw_sources[c['module']]+b'\n'+probes[c['module']]);bound.add(fixture)
(RUNTIME/'IndependentProbes.lean').write_bytes(independent)
for src,dst in [('shadow-compile.py.txt','shadow-compile.py'),('strict-bind.py.txt','strict-new-and-bind.py'),('publication-driver.py.txt','check.py')]:
    (RUNTIME/dst).write_bytes((CONTROL/src).read_bytes())
(RUNTIME/'REPORT-BASE.json').write_bytes((CONTROL/'REPORT-BASE.json').read_bytes())
selection = {'compile_order':stage['compile_order'],'prior_checkpoint':CHECKPOINT,
    'prior_archive_manifest_sha256':read(PRIOR/'PUSH-VERIFIED.json')['archive_manifest_sha256'],
    'prior_checked_sha256':SHA((PRIOR_RUN/'checked.json').read_bytes()),'prior_pins_sha256':SHA((PRIOR_RUN/'source-pins.json').read_bytes()),
    'stage_sha256':SHA(stage_bytes),'baseline_path':stage['source_baseline_path'],'baseline_sha256':stage['source_baseline_sha256'],
    'baseline_overrides':OVERRIDES,'override_digests':{n:SHA((ROOT/p).read_bytes()) for n,p in OVERRIDES.items()},
    'inherited_reports':540,'fresh_public_reports':2,'fresh_private_reports':3,'combined_reports':545,
    'fresh_axiom_groups':classification['all']['axiom_groups'],'fresh_axiom_free_reports':classification['all']['axiom_free_reports'],
    'fresh_public_axiom_groups':classification['public']['axiom_groups'],'fresh_public_axiom_free_reports':classification['public']['axiom_free_reports'],
    'independent_axiom_groups':prior['checks'][2]['axiom_groups']+classification['public']['axiom_groups'],
    'independent_axiom_free_reports':prior['checks'][2]['axiom_free_reports']+classification['public']['axiom_free_reports'],
    'audit_axiom_groups':prior['checks'][4]['axiom_groups']+classification['public']['axiom_groups'],
    'audit_axiom_free_reports':prior['checks'][4]['axiom_free_reports']+classification['public']['axiom_free_reports'],
    'actual_private_session':verified['actual_session'],'new_public_theorems':2,'new_private_theorems':6,'fresh_reported_private_laws':3,
    'new_private_helpers_transitive':3,'new_definitions':0,'definition_checks':0,'definition_axiom_credit':0,
    'inherited_independent_checks':300,'resource_owner_reports_inherited':264,'fresh_credit_for_old_owner_theorems':0,
    'rebuilt_Source65_leaf_and_zero_base_extra_credit':0,'cache_data_copied':False}
(RUNTIME/'INHERITANCE-SELECTION.json').write_text(json.dumps(selection,indent=2)+'\n')
bound.add(Path(__file__));bound.update((ROOT/'lean/MicroCFTA').glob('*.lean'))
bound.update(path for path in RUNTIME.iterdir() if path.is_file())
(RUNTIME/'source-pins.json').write_text(json.dumps({str(path.relative_to(ROOT)):SHA(path.read_bytes()) for path in sorted(bound)},indent=2,sort_keys=True)+'\n')
print(json.dumps({'runtime':str(RUNTIME),'gates':5,'strict_owning_commands':3,'fresh_public_reports':2,'fresh_private_reports':3,
    'new_private_helpers_transitive':3,'new_definitions':0,'source_files':6286,'audit_imports':5286,'audit_reports':746,'independent_reports':341,'normal_Source_changed':False}))
