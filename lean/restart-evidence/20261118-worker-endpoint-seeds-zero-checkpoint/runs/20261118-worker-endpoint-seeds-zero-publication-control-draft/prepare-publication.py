from pathlib import Path
import ast
import hashlib
import json
import tempfile

ROOT = Path('/home/tritlo/Code/mcfta')
BASE = ROOT/'lean/restart-evidence'
CONTROL = BASE/'20261118-worker-endpoint-seeds-zero-publication-control-draft'
STAGE_CONTROL = BASE/'20261118-worker-endpoint-seeds-zero-staging-control-draft'
WORK = BASE/'20261118-worker-endpoint-seeds-zero-work'
RUNTIME = BASE/'20261118-worker-endpoint-seeds-zero-publication'
assert (CONTROL/'STATUS.txt').read_text().startswith('FROZEN'), 'OPEN control; do not execute.'
assert Path(__file__).resolve().parent == WORK.resolve()
assert Path(__file__).read_bytes() == (CONTROL/'prepare-publication.py').read_bytes()
assert not RUNTIME.exists(), 'Preserve every prior runtime.'
stage_bytes = (WORK/'SOURCES-NORMAL-STAGING.json').read_bytes()
assert stage_bytes == (CONTROL/'EXPECTED-STAGE.json').read_bytes()
stage = json.loads(stage_bytes)
assert stage['status'] == 'SOURCE_NORMAL_STAGING_COMPLETED'
assert stage['normal_Source_changed'] and not stage['published'] and not stage['Audit_changed']
OVERRIDES = stage['baseline_overrides']
assert set(OVERRIDES) == {'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'}
exec(compile((CONTROL/'validate-inputs.py.txt').read_text(),str(CONTROL/'validate-inputs.py.txt'),'exec'))
baseline,component,raw,probes,leaf,zero,prior,classification = preflight(CONTROL)
packet(STAGE_CONTROL,read(CONTROL/'STAGING-BINDING.json')['control_manifest_sha256'])
actual_path = WORK/'STAGING-ACTUAL-RUN.json'
actual = read(actual_path)
assert actual == read(CONTROL/'EXPECTED-STAGING-ACTUAL-RUN.json')
assert actual['actual_terminal'] and actual['actual_terminal_exit'] == 0
assert actual['control_manifest_sha256'] == SHA((STAGE_CONTROL/'MANIFEST.json').read_bytes())
assert actual['script_sha256'] == SHA((STAGE_CONTROL/'stage-normal-sources.py').read_bytes())
assert actual['exact_Source_write_paths'] == stage['exact_Source_write_paths'] == [OWNER]
assert actual['git_index_empty']
assert actual['normal_source_pins_sha256'] == stage['normal_source_pins_sha256']
assert stage['fresh_classification'] == classification
assert stage['actual_private_sessions'] == [leaf[0]['actual_session'],zero[0]['actual_session']]
normal_pins = pin_map(WORK/'NORMAL-SOURCE-PINS.json',stage['normal_source_pins_sha256'],6290)
assert normal_pins[OWNER] == SHA(raw)
assert (ROOT/OWNER).read_bytes() == raw
assert set(normal_pins) == set(baseline['sources'])|set(baseline['toolchain'])
for name,record in {**baseline['sources'],**baseline['toolchain']}.items():
    assert normal_pins[name] == (SHA(raw) if name == OWNER else record['sha256'])
assert len((ROOT/'lean/MicroCFTA/Audit.lean').read_bytes()) == 436723
assert SHA((ROOT/'lean/MicroCFTA/Audit.lean').read_bytes()) == baseline['sources']['lean/MicroCFTA/Audit.lean']['sha256']
prior_independent = verify(PRIOR_RUN/'IndependentProbes.lean',read(CONTROL/'PRIOR-INDEPENDENT.json')['sha256'])
assert prior_independent.count(b'#print axioms ') == 339
assert b'#check ' not in prior_independent
normal_objects = ROOT/'lean/.lake/build/lib/lean/MicroCFTA'
assert normal_objects.is_dir()
for module in read(CONTROL/'TOPOLOGICAL-ORDER.json')['full_transitive_order']:
    if module != component['module']:
        assert (normal_objects/(module+'.olean')).is_file(),module
for filename in ['shadow-compile.py.txt','strict-bind.py.txt','publication-driver.py.txt']:
    ast.parse((CONTROL/filename).read_text())
bound.update([WORK/'SOURCES-NORMAL-STAGING.json',actual_path,WORK/'NORMAL-SOURCE-PINS.json',PRIOR_RUN/'IndependentProbes.lean'])
# Root creates a fresh namespace after every read-only gate passes. No object is copied.
RUNTIME.mkdir()
objects = Path(tempfile.mkdtemp(prefix='mcfta-worker-endpoint-seeds-zero-publication-'))
(objects/'MicroCFTA').mkdir()
for obj in normal_objects.glob('*.olean'):
    if obj.stem != component['module']:
        (objects/'MicroCFTA'/obj.name).symlink_to(obj)
assert not (objects/'MicroCFTA'/(component['module']+'.olean')).exists()
(RUNTIME/'objects.json').write_text(json.dumps({'path':str(objects)},indent=2)+'\n')
fixture = RUNTIME/'source/MicroCFTA'/component['source']
fixture.parent.mkdir(parents=True)
fixture.write_bytes(raw+b'\n'+probes)
(RUNTIME/'IndependentProbes.lean').write_bytes(prior_independent)
for src,dst in [('shadow-compile.py.txt','shadow-compile.py'),('strict-bind.py.txt','strict-new-and-bind.py'),('publication-driver.py.txt','check.py')]:
    (RUNTIME/dst).write_bytes((CONTROL/src).read_bytes())
(RUNTIME/'REPORT-BASE.json').write_bytes((CONTROL/'REPORT-BASE.json').read_bytes())
selection = {'compile_order':[component['module']],'private_qnames':component['private_qnames'],'definition_names':component['definition_qnames'],
    'definition_owner':component['module'],'prior_checkpoint':CHECKPOINT,'prior_archive_manifest_sha256':read(PRIOR/'PUSH-VERIFIED.json')['archive_manifest_sha256'],
    'prior_checked_sha256':SHA((PRIOR_RUN/'checked.json').read_bytes()),'prior_pins_sha256':SHA((PRIOR_RUN/'source-pins.json').read_bytes()),
    'stage_sha256':SHA(stage_bytes),'baseline_path':stage['source_baseline_path'],'baseline_sha256':stage['source_baseline_sha256'],
    'baseline_overrides':OVERRIDES,'override_digests':{name:SHA((ROOT/path).read_bytes()) for name,path in OVERRIDES.items()},
    'inherited_reports':538,'fresh_public_reports':0,'fresh_private_reports':2,'combined_reports':540,
    'fresh_axiom_groups':classification['axiom_groups'],'fresh_axiom_free_reports':classification['axiom_free_reports'],
    'independent_axiom_groups':prior['checks'][2]['axiom_groups'],'independent_axiom_free_reports':prior['checks'][2]['axiom_free_reports'],
    'audit_axiom_groups':prior['checks'][4]['axiom_groups'],'audit_axiom_free_reports':prior['checks'][4]['axiom_free_reports'],
    'new_private_theorems':2,'new_private_helpers':0,'Prop_declaration_checks':3,'Prop_axiom_credit':0,
    'resource_owner_reports_inherited':264,'fresh_credit_for_old_owner_theorems':0,
    'actual_private_sessions':[leaf[0]['actual_session'],zero[0]['actual_session']],'rebuilt_prior_leaf_extra_credit':0,'cache_data_copied':False}
(RUNTIME/'INHERITANCE-SELECTION.json').write_text(json.dumps(selection,indent=2)+'\n')
bound.add(Path(__file__)); bound.add(fixture)
bound.update(path for path in (ROOT/'lean/MicroCFTA').glob('*.lean'))
bound.update(path for path in RUNTIME.iterdir() if path.is_file())
pins = {str(path.relative_to(ROOT)):SHA(path.read_bytes()) for path in sorted(bound)}
(RUNTIME/'source-pins.json').write_text(json.dumps(pins,indent=2,sort_keys=True)+'\n')
print(json.dumps({'runtime':str(RUNTIME),'gates':5,'fresh_public_reports':0,'fresh_private_reports':2,'definition_checks':3,
    'definition_axiom_credit':0,'source_files':6286,'audit_imports':5286,'audit_reports':744,'independent_reports':339,'Audit_changed':False,'normal_Source_changed':False}))
