from pathlib import Path
import ast
import json
import tempfile

ROOT = Path('/home/tritlo/Code/mcfta')
BASE = ROOT/'lean/restart-evidence'
CONTROL = BASE/'20261118-worker-current-seeds-publication-control-draft'
STAGE_CONTROL = BASE/'20261118-worker-current-seeds-staging-control-draft'
WORK = BASE/'20261118-worker-inner-selected-prefix-seeds-work'
RUNTIME = BASE/'20261118-worker-current-seeds-publication'
assert (CONTROL/'STATUS.txt').read_text().startswith('FROZEN'), 'OPEN control; do not execute.'
assert Path(__file__).resolve().parent == WORK.resolve()
assert Path(__file__).read_bytes() == (CONTROL/'prepare-publication.py').read_bytes()
assert not RUNTIME.exists(), 'Preserve every previous runtime.'
stage_bytes = (WORK/'SOURCES-NORMAL-STAGING.json').read_bytes()
assert stage_bytes == (CONTROL/'EXPECTED-STAGE.json').read_bytes()
stage = json.loads(stage_bytes)
assert stage['status'] == 'SOURCE_NORMAL_STAGING_COMPLETED' and stage['normal_Source_changed'] and not stage['published']
OVERRIDES = stage['baseline_overrides']
assert set(OVERRIDES) == {'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'}
exec(compile((CONTROL/'validate-inputs.py.txt').read_text(),str(CONTROL/'validate-inputs.py.txt'),'exec'))
stage,baseline,component,raw,probes,bundles,prior,classification = preflight(CONTROL)
packet(STAGE_CONTROL,read(CONTROL/'STAGING-BINDING.json')['control_manifest_sha256'])
stage_actual = read(WORK/'STAGING-ACTUAL-RUN.json')
assert stage_actual == read(CONTROL/'EXPECTED-STAGING-ACTUAL-RUN.json')
assert stage_actual['actual_terminal'] and stage_actual['actual_terminal_exit'] == 0
assert stage_actual['control_manifest_sha256'] == SHA((STAGE_CONTROL/'MANIFEST.json').read_bytes())
assert stage_actual['script_sha256'] == SHA((STAGE_CONTROL/'stage-normal-sources.py').read_bytes())
assert stage_actual['exact_Source_write_paths'] == stage['exact_Source_write_paths'] and stage_actual['git_index_empty']
assert stage_actual['normal_source_pins_sha256'] == stage['normal_source_pins_sha256']
assert stage['fresh_classification'] == classification and stage['actual_private_sessions'] == [entry['verified']['actual_session'] for entry in bundles]
normal_pins = pin_map(WORK/'NORMAL-SOURCE-PINS.json',stage['normal_source_pins_sha256'],6290)
assert (ROOT/OWNER).read_bytes() == raw and normal_pins[OWNER] == SHA(raw)
for name,record in {**baseline['sources'],**baseline['toolchain']}.items():
    assert normal_pins[name] == (SHA(raw) if name == OWNER else record['sha256'])
assert len(set(baseline['sources'])-{OWNER}) == 6285
new_audit = (ROOT/'lean/MicroCFTA/Audit.lean').read_bytes()
assert SHA(new_audit) == baseline['sources']['lean/MicroCFTA/Audit.lean']['sha256']
assert len(new_audit) == 436889 and new_audit.count(b'#print axioms ') == 746 and len(re.findall(rb'^import ',new_audit,re.M)) == 5286
prior_independent = verify(PRIOR_RUN/'IndependentProbes.lean',read(CONTROL/'PRIOR-INDEPENDENT.json')['sha256'])
assert prior_independent.count(b'#print axioms ') == 341 and prior_independent.count(b'#check ') == 300
assert all(q.encode() not in prior_independent for q in component['private_qnames'])
# The independent public fixture stays byte exact. The fifteen private laws are queried only in their owning file.
independent = prior_independent
normal_objects = ROOT/'lean/.lake/build/lib/lean/MicroCFTA'
assert normal_objects.is_dir()
for module in read(CONTROL/'TOPOLOGICAL-ORDER.json')['full_transitive_order']:
    if module != component['module']:
        assert (normal_objects/(module+'.olean')).is_file(),module
for name in ['shadow-compile.py.txt','strict-bind.py.txt','publication-driver.py.txt']:
    ast.parse((CONTROL/name).read_text())
bound.update([WORK/'SOURCES-NORMAL-STAGING.json',WORK/'STAGING-ACTUAL-RUN.json',WORK/'NORMAL-SOURCE-PINS.json',PRIOR_RUN/'IndependentProbes.lean'])
# Root materializes one fresh owning-module output. No compiled object is copied.
RUNTIME.mkdir()
objects = Path(tempfile.mkdtemp(prefix='mcfta-worker-current-seeds-publication-'))
(objects/'MicroCFTA').mkdir()
for obj in normal_objects.glob('*.olean'):
    if obj.stem != component['module']:
        (objects/'MicroCFTA'/obj.name).symlink_to(obj)
assert not(objects/'MicroCFTA'/(component['module']+'.olean')).exists()
(RUNTIME/'objects.json').write_text(json.dumps({'path':str(objects)},indent=2)+'\n')
fixture = RUNTIME/'source/MicroCFTA'/component['source'];fixture.parent.mkdir(parents=True,exist_ok=True)
fixture.write_bytes(raw+b'\n'+probes);bound.add(fixture)
(RUNTIME/'IndependentProbes.lean').write_bytes(independent)
for src,dst in [('shadow-compile.py.txt','shadow-compile.py'),('strict-bind.py.txt','strict-new-and-bind.py'),('publication-driver.py.txt','check.py')]:
    (RUNTIME/dst).write_bytes((CONTROL/src).read_bytes())
(RUNTIME/'REPORT-BASE.json').write_bytes((CONTROL/'REPORT-BASE.json').read_bytes())
selection = dict(compile_order=stage['compile_order'],prior_checkpoint=CHECKPOINT,
    prior_archive_manifest_sha256=read(PRIOR/'PUSH-VERIFIED.json')['archive_manifest_sha256'],
    prior_checked_sha256=SHA((PRIOR_RUN/'checked.json').read_bytes()),prior_pins_sha256=SHA((PRIOR_RUN/'source-pins.json').read_bytes()),
    stage_sha256=SHA(stage_bytes),baseline_path=stage['source_baseline_path'],baseline_sha256=stage['source_baseline_sha256'],
    baseline_overrides=OVERRIDES,override_digests={n:SHA((ROOT/p).read_bytes()) for n,p in OVERRIDES.items()},
    inherited_reports=545,fresh_public_reports=0,fresh_private_reports=15,combined_reports=560,
    fresh_axiom_groups=classification['axiom_groups'],fresh_axiom_free_reports=classification['axiom_free_reports'],
    independent_axiom_groups=prior['checks'][2]['axiom_groups'],independent_axiom_free_reports=prior['checks'][2]['axiom_free_reports'],
    audit_axiom_groups=prior['checks'][4]['axiom_groups'],audit_axiom_free_reports=prior['checks'][4]['axiom_free_reports'],
    actual_private_sessions=[entry['verified']['actual_session'] for entry in bundles],new_public_theorems=0,new_private_theorems=15,new_private_helpers_transitive=0,
    new_definitions=0,definition_checks=0,definition_axiom_credit=0,inherited_independent_checks=300,
    resource_owner_reports_inherited=264,fresh_credit_for_old_owner_theorems=0,rebuilt_Source66_steps_extra_credit=0,cache_data_copied=False)
(RUNTIME/'INHERITANCE-SELECTION.json').write_text(json.dumps(selection,indent=2)+'\n')
bound.add(Path(__file__));bound.update((ROOT/'lean/MicroCFTA').glob('*.lean'))
bound.update(p for p in RUNTIME.iterdir() if p.is_file())
(RUNTIME/'source-pins.json').write_text(json.dumps({str(p.relative_to(ROOT)):SHA(p.read_bytes()) for p in sorted(bound)},indent=2,sort_keys=True)+'\n')
print(json.dumps(dict(runtime=str(RUNTIME),gates=5,strict_owning_commands=1,fresh_public_reports=0,fresh_private_reports=15,
    new_private_helpers_transitive=0,new_definitions=0,source_files=6286,audit_imports=5286,audit_reports=746,independent_reports=341,normal_Source_changed=False)))
