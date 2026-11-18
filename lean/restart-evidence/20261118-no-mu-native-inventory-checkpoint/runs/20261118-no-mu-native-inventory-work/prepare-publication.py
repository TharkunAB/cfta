from pathlib import Path
import ast
import json
import tempfile
ROOT = Path('/home/tritlo/Code/mcfta')
BASE = ROOT/'lean/restart-evidence'
CONTROL = BASE/'20261118-no-mu-native-inventory-publication-control-draft'
STAGE_CONTROL = BASE/'20261118-no-mu-native-inventory-staging-control-draft'
WORK = BASE/'20261118-no-mu-native-inventory-work'
RUNTIME = BASE/'20261118-no-mu-native-inventory-publication'
assert Path(__file__).resolve().parent == WORK and Path(__file__).read_bytes() == (CONTROL/'prepare-publication.py').read_bytes()
assert not RUNTIME.exists()
stage_bytes = (WORK/'SOURCES-NORMAL-STAGING.json').read_bytes()
assert stage_bytes == (CONTROL/'EXPECTED-STAGE.json').read_bytes()
OVERRIDES = json.loads(stage_bytes)['baseline_overrides']
exec(compile((CONTROL/'validate-inputs.py.txt').read_text(),str(CONTROL/'validate-inputs.py.txt'),'exec'))
stage,baseline,component,raw,probe,audit,verified,prior,classification = preflight(CONTROL)
assert stage['status'] == 'SOURCE_NORMAL_STAGING_COMPLETED' and stage['normal_Source_changed']
packet(STAGE_CONTROL,read(CONTROL/'STAGING-BINDING.json')['control_manifest_sha256'])
actual_stage = read(WORK/'STAGING-ACTUAL-RUN.json')
assert actual_stage == read(CONTROL/'EXPECTED-STAGING-ACTUAL-RUN.json') and actual_stage['actual_terminal'] and actual_stage['actual_terminal_exit'] == 0 and actual_stage['git_index_empty']
assert actual_stage['control_manifest_sha256'] == SHA((STAGE_CONTROL/'MANIFEST.json').read_bytes()) and actual_stage['script_sha256'] == SHA((STAGE_CONTROL/'stage-normal-sources.py').read_bytes())
assert stage['fresh_classification'] == classification and stage['actual_private_session'] == verified['actual_session']
normal = json.loads(verify(WORK/'NORMAL-SOURCE-PINS.json',stage['normal_source_pins_sha256']))
assert len(normal) == 6295
for name,digest in normal.items():
    verify(ROOT/name,digest)
assert (ROOT/component['source_path']).read_bytes() == raw and (ROOT/AUDIT).read_bytes() == audit
old_independent = (PRIOR_RUN/'IndependentProbes.lean').read_bytes()
assert old_independent.count(b'#print axioms ') == 346 and old_independent.count(b'#check ') == 300
assert component['public_qnames'][0].encode() not in old_independent
imports = (CONTROL/'IMPORTS.lean.txt').read_bytes()
independent = imports+old_independent+b'\n'+probe
assert independent[50:50+len(old_independent)] == old_independent
assert independent.count(b'#print axioms ') == 347 and independent.count(b'#check ') == 300
normal_objects = ROOT/'lean/.lake/build/lib/lean/MicroCFTA'
for module in read(CONTROL/'TOPOLOGICAL-ORDER.json')['full_transitive_order']:
    if module != component['module']:
        assert (normal_objects/(module+'.olean')).is_file(),module
for name in ['publication-driver.py.txt','strict-bind.py.txt','shadow-compile.py.txt']:
    ast.parse((CONTROL/name).read_text())
bound.update([WORK/'SOURCES-NORMAL-STAGING.json',WORK/'STAGING-ACTUAL-RUN.json',WORK/'NORMAL-SOURCE-PINS.json',PRIOR_RUN/'IndependentProbes.lean'])
# Root links normal dependencies and produces one fresh selected object.
RUNTIME.mkdir()
objects = Path(tempfile.mkdtemp(prefix='mcfta-no-mu-native-inventory-publication-'))
(objects/'MicroCFTA').mkdir()
for obj in normal_objects.glob('*.olean'):
    if obj.stem != component['module']:
        (objects/'MicroCFTA'/obj.name).symlink_to(obj)
assert not (objects/'MicroCFTA'/(component['module']+'.olean')).exists()
fixture = RUNTIME/'source/MicroCFTA'/component['source']
fixture.parent.mkdir(parents=True)
fixture.write_bytes(raw+b'\n'+probe)
bound.add(fixture)
(RUNTIME/'objects.json').write_text(json.dumps({'path':str(objects)},indent=2)+'\n')
(RUNTIME/'IndependentProbes.lean').write_bytes(independent)
for src,dst in [('shadow-compile.py.txt','shadow-compile.py'),('strict-bind.py.txt','strict-new-and-bind.py'),('publication-driver.py.txt','check.py')]:
    (RUNTIME/dst).write_bytes((CONTROL/src).read_bytes())
(RUNTIME/'REPORT-BASE.json').write_bytes((CONTROL/'REPORT-BASE.json').read_bytes())
selection = dict(compile_order=[component['module']],prior_checkpoint=CHECKPOINT,prior_archive_manifest_sha256=read(PRIOR/'PUSH-VERIFIED.json')['archive_manifest_sha256'],prior_checked_sha256=SHA((PRIOR_RUN/'checked.json').read_bytes()),prior_pins_sha256=SHA((PRIOR_RUN/'source-pins.json').read_bytes()),stage_sha256=SHA(stage_bytes),baseline_path=stage['source_baseline_path'],baseline_sha256=stage['source_baseline_sha256'],baseline_overrides=OVERRIDES,override_digests={n:SHA((ROOT/p).read_bytes()) for n,p in OVERRIDES.items()},fresh_axiom_groups=classification['axiom_groups'],fresh_axiom_free_reports=classification['axiom_free_reports'],fresh_per_qname_classification=classification['per_qname'],independent_axiom_groups=prior['checks'][2]['axiom_groups']+classification['axiom_groups'],independent_axiom_free_reports=prior['checks'][2]['axiom_free_reports']+classification['axiom_free_reports'],audit_axiom_groups=prior['checks'][4]['axiom_groups']+classification['axiom_groups'],audit_axiom_free_reports=prior['checks'][4]['axiom_free_reports']+classification['axiom_free_reports'],actual_private_sessions=[verified['actual_session']],inherited_reports=568,fresh_public_reports=1,fresh_private_reports=0,combined_reports=569,inherited_independent_checks=300,resource_owner_reports_inherited=264)
(RUNTIME/'INHERITANCE-SELECTION.json').write_text(json.dumps(selection,indent=2)+'\n')
bound.add(Path(__file__));bound.update((ROOT/'lean/MicroCFTA').glob('*.lean'));bound.update(p for p in RUNTIME.iterdir() if p.is_file())
(RUNTIME/'source-pins.json').write_text(json.dumps({str(p.relative_to(ROOT)):SHA(p.read_bytes()) for p in sorted(bound)},indent=2,sort_keys=True)+'\n')
print(json.dumps(dict(runtime=str(RUNTIME),gates=5,fresh_public_reports=1,fresh_private_reports=0,source_files=6291,audit_imports=5291,audit_reports=752,independent_reports=347)))
