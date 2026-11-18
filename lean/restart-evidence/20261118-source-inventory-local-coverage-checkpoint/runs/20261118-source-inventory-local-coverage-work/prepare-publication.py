from pathlib import Path
import ast
import json
import tempfile
ROOT = Path('/home/tritlo/Code/mcfta')
BASE = ROOT/'lean/restart-evidence'
CONTROL = BASE/'20261118-source-inventory-local-coverage-publication-control-draft'
STAGE_CONTROL = BASE/'20261118-source-inventory-local-coverage-staging-control-draft'
WORK = BASE/'20261118-source-inventory-local-coverage-work'
RUNTIME = BASE/'20261118-source-inventory-local-coverage-publication'
assert (CONTROL/'STATUS.txt').read_text().startswith('FROZEN'),'OPEN control; do not execute.'
assert Path(__file__).resolve().parent == WORK.resolve() and Path(__file__).read_bytes() == (CONTROL/'prepare-publication.py').read_bytes()
assert not RUNTIME.exists(),'Preserve all prior runtimes.'
stage_bytes = (WORK/'SOURCES-NORMAL-STAGING.json').read_bytes()
assert stage_bytes == (CONTROL/'EXPECTED-STAGE.json').read_bytes()
stage = json.loads(stage_bytes)
OVERRIDES = stage['baseline_overrides']
exec(compile((CONTROL/'validate-inputs.py.txt').read_text(),str(CONTROL/'validate-inputs.py.txt'),'exec'))
stage,baseline,components,raws,probes,audit,verified,prior,classification = preflight(CONTROL)
assert stage['status'] == 'SOURCE_NORMAL_STAGING_COMPLETED' and stage['normal_Source_changed'] and not stage['published']
packet(STAGE_CONTROL,read(CONTROL/'STAGING-BINDING.json')['control_manifest_sha256'])
actual_stage = read(WORK/'STAGING-ACTUAL-RUN.json')
assert actual_stage == read(CONTROL/'EXPECTED-STAGING-ACTUAL-RUN.json') and actual_stage['actual_terminal'] and actual_stage['actual_terminal_exit'] == 0
assert actual_stage['control_manifest_sha256'] == SHA((STAGE_CONTROL/'MANIFEST.json').read_bytes()) and actual_stage['script_sha256'] == SHA((STAGE_CONTROL/'stage-normal-sources.py').read_bytes())
assert actual_stage['exact_Source_write_paths'] == stage['exact_Source_write_paths'] and actual_stage['git_index_empty']
assert stage['fresh_classification'] == classification and stage['actual_private_session'] == verified['actual_session']
normal_pins = json.loads(verify(WORK/'NORMAL-SOURCE-PINS.json',stage['normal_source_pins_sha256']))
assert len(normal_pins) == 6294
for name,digest in normal_pins.items():
    verify(ROOT/name,digest)
for component in components:
    assert (ROOT/component['source_path']).read_bytes() == raws[component['module']]
assert (ROOT/AUDIT).read_bytes() == audit and len(list((ROOT/'lean/MicroCFTA').glob('*.lean'))) == 6290
public = (CONTROL/'PUBLIC-PROBES.lean.txt').read_bytes()
prior_independent = (PRIOR_RUN/'IndependentProbes.lean').read_bytes()
assert prior_independent.count(b'#print axioms ') == 344 and prior_independent.count(b'#check ') == 300
assert all(q.encode() not in prior_independent for e in components for q in e['private_qnames']+e['public_qnames']+e['definition_qnames'])
imports = (CONTROL/'IMPORTS.lean.txt').read_bytes()
assert imports == ''.join('import MicroCFTA.'+e['module']+'\n' for e in components if e['new_module']).encode() and len(imports) == 131
independent = imports+prior_independent+b'\n'+public
assert independent[131:131+len(prior_independent)] == prior_independent
assert independent.count(b'#print axioms ') == 346 and independent.count(b'#check ') == 300
normal_objects = ROOT/'lean/.lake/build/lib/lean/MicroCFTA'
for module in read(CONTROL/'TOPOLOGICAL-ORDER.json')['full_transitive_order']:
    if module not in stage['compile_order']:
        assert (normal_objects/(module+'.olean')).is_file(),module
for name in ['publication-driver.py.txt','strict-bind.py.txt','shadow-compile.py.txt']:
    ast.parse((CONTROL/name).read_text())
bound.update([WORK/'SOURCES-NORMAL-STAGING.json',WORK/'STAGING-ACTUAL-RUN.json',WORK/'NORMAL-SOURCE-PINS.json',PRIOR_RUN/'IndependentProbes.lean'])
# Root creates fresh outputs for all three selected owners. No object data is copied.
RUNTIME.mkdir()
objects = Path(tempfile.mkdtemp(prefix='mcfta-source-inventory-local-coverage-publication-'))
(objects/'MicroCFTA').mkdir()
for obj in normal_objects.glob('*.olean'):
    if obj.stem not in stage['compile_order']:
        (objects/'MicroCFTA'/obj.name).symlink_to(obj)
for component in components:
    assert not (objects/'MicroCFTA'/(component['module']+'.olean')).exists()
    fixture = RUNTIME/'source/MicroCFTA'/(component['module']+'.lean')
    fixture.parent.mkdir(parents=True,exist_ok=True)
    fixture.write_bytes(raws[component['module']]+b'\n'+probes[component['module']]);bound.add(fixture)
(RUNTIME/'objects.json').write_text(json.dumps({'path':str(objects)},indent=2)+'\n')
(RUNTIME/'IndependentProbes.lean').write_bytes(independent)
for src,dst in [('shadow-compile.py.txt','shadow-compile.py'),('strict-bind.py.txt','strict-new-and-bind.py'),('publication-driver.py.txt','check.py')]:
    (RUNTIME/dst).write_bytes((CONTROL/src).read_bytes())
(RUNTIME/'REPORT-BASE.json').write_bytes((CONTROL/'REPORT-BASE.json').read_bytes())
selection = dict(compile_order=stage['compile_order'],prior_checkpoint=CHECKPOINT,prior_archive_manifest_sha256=read(PRIOR/'PUSH-VERIFIED.json')['archive_manifest_sha256'],prior_checked_sha256=SHA((PRIOR_RUN/'checked.json').read_bytes()),prior_pins_sha256=SHA((PRIOR_RUN/'source-pins.json').read_bytes()),stage_sha256=SHA(stage_bytes),baseline_path=stage['source_baseline_path'],baseline_sha256=stage['source_baseline_sha256'],baseline_overrides=OVERRIDES,override_digests={n:SHA((ROOT/p).read_bytes())for n,p in OVERRIDES.items()},inherited_reports=564,fresh_public_reports=2,fresh_private_reports=2,combined_reports=568,fresh_axiom_groups=classification['axiom_groups'],fresh_axiom_free_reports=classification['axiom_free_reports'],fresh_per_qname_classification=classification['per_qname'],independent_axiom_groups=prior['checks'][2]['axiom_groups']+classification['public']['axiom_groups'],independent_axiom_free_reports=prior['checks'][2]['axiom_free_reports']+classification['public']['axiom_free_reports'],audit_axiom_groups=prior['checks'][4]['axiom_groups']+classification['public']['axiom_groups'],audit_axiom_free_reports=prior['checks'][4]['axiom_free_reports']+classification['public']['axiom_free_reports'],actual_private_sessions=[verified['actual_session']],new_public_theorems=2,new_private_theorems=2,new_private_helpers_transitive=0,new_definitions=0,definition_checks=0,new_private_Prop_inductives=0,new_constructors=0,definition_qnames=[],definition_axiom_credit=0,inherited_independent_checks=300,resource_owner_reports_inherited=264,fresh_credit_for_old_owner_theorems=0,rebuilt_Source69_Prop_relations_and_36_constructors_extra_credit=0,rebuilt_Source69_generated_brecOn_extra_credit=0,old_generic_Mu_actual22743_additive_credit=0,cache_data_copied=False)
(RUNTIME/'INHERITANCE-SELECTION.json').write_text(json.dumps(selection,indent=2)+'\n')
bound.add(Path(__file__));bound.update((ROOT/'lean/MicroCFTA').glob('*.lean'));bound.update(p for p in RUNTIME.iterdir()if p.is_file())
(RUNTIME/'source-pins.json').write_text(json.dumps({str(p.relative_to(ROOT)):SHA(p.read_bytes())for p in sorted(bound)},indent=2,sort_keys=True)+'\n')
print(json.dumps(dict(runtime=str(RUNTIME),gates=5,strict_owning_commands=3,fresh_public_reports=2,fresh_private_reports=2,new_definitions=0,definition_checks=0,source_files=6290,audit_imports=5290,audit_reports=751,independent_reports=346)))
