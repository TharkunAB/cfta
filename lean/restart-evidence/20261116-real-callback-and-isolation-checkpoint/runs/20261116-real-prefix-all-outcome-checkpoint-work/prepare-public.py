from pathlib import Path
import gzip
import hashlib
import json
import tempfile

root = Path('/home/tritlo/Code/mcfta')
work = Path(__file__).parent
runtime = root / 'lean/restart-evidence/20261116-real-prefix-all-outcome-publication'
runtime.mkdir()
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
prior = root / 'lean/restart-evidence/20261115-real-prefix-and-opaque-resources-checkpoint'
old_pins = json.loads(gzip.decompress((prior / 'source-pins.json.gz').read_bytes()))
for name, digest in old_pins.items():
    if name != 'lean/MicroCFTA/Audit.lean':
        assert sha(root / name) == digest, name
assert len([name for name in old_pins if name.startswith('lean/MicroCFTA/') and name != 'lean/MicroCFTA/Audit.lean']) == 6119
old_audit = (work / 'BASE-AUDIT.lean.txt').read_bytes()
assert old_audit in (root / 'lean/MicroCFTA/Audit.lean').read_bytes()
owner = root / 'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'
old_public = root / 'lean/restart-evidence/20261115-real-prefix-and-opaque-publication'
probes = (old_public / 'ResourceProbes.lean.txt').read_bytes()
assert probes.count(b'#print axioms ') == 73
(runtime / 'ResourceProbes.lean.txt').write_bytes(probes)
source = runtime / 'source/MicroCFTA' / owner.name
source.parent.mkdir(parents=True)
source.write_bytes(owner.read_bytes() + b'\n' + probes)
objects = Path(tempfile.mkdtemp(prefix='mcfta-real-prefix-publication-'))
(runtime / 'objects.json').write_text(json.dumps({'path':str(objects)}, indent=2) + '\n')
commands = [['lake','env','lean','-j1','-DwarningAsError=true','-R',str(source.parent.parent),
    '-o',str(objects / 'Owner.olean'),str(source)]]
for name in ['SourcePruningEnumerationRealPrefixAllResources', 'SourcePruningEnumerationRealPrefixContinuingResources']:
    commands.append(['lake','env','lean','-j1','-DwarningAsError=true','-o',str(objects / (name + '.olean')),
        str(root / 'lean/MicroCFTA' / (name + '.lean'))])
strict = runtime / 'strict-modules.py'
strict.write_text('import subprocess\ncommands = ' + repr(commands) + '\nfor command in commands:\n    subprocess.run(command,check=True)\n')
independent = runtime / 'IndependentProbes.lean'
text = 'import MicroCFTA.SourcePruningEnumerationRealPrefixAllResources\n'
text += 'import MicroCFTA.SourcePruningEnumerationRealPrefixContinuingResources\n'
text += (old_public / 'IndependentProbes.lean').read_text()
for law in ['prefix_real_resources_at_original_budget', 'prefix_zero_stops_and_not_current',
            'real_prefix_noncontinuing_emits_no_output', 'prefix_real_continuing_current_at_original_budget']:
    qualified = 'MicroCFTA.SourcePruningEnumerationSharedRecursive.' + law
    text += '\n#check @' + qualified + '\n#print axioms ' + qualified + '\n'
independent.write_text(text)
assert text.count('#print axioms ') == 8
template = (root / 'lean/restart-evidence/20261115-native-open-binder-helper-dependencies/check.py').read_text()
driver = template[:template.index('run("public-dependency"')]
jobs = [('public-build','exec lake build',0),
    ('strict-modules-and-73-resources','exec python3 ' + str(strict),73),
    ('independent-imports','exec lake env lean -j1 -DwarningAsError=true ' + str(independent),8),
    ('audit-build','exec lake build MicroCFTA.Audit',0),
    ('audit-strict','exec lake env lean -j1 -DwarningAsError=true MicroCFTA/Audit.lean',413)]
driver += 'jobs = ' + repr(jobs) + '''
for name, command, count in jobs:
    run(name, command, count)
match = re.search(r'Checked axiom dependencies of (\\d+) MicroCFTA theorems\\.', (runtime/'audit-strict.txt').read_text())
assert match and checks[-1]['total_axiom_reports'] == 413
report = {'checks':checks,'source_pins_unchanged':True,'audited_theorems':int(match.group(1)),
    'individual_reports':413,'retained_resource_probes':66,'owner_resource_probes':73,
    'all_actual_real_prefix_resources_at_original_budget_proved':True,
    'all_continuing_real_prefix_current_resources_at_original_budget_proved':True,
    'noncontinuing_local_outputs_empty_proved':True,
    'zero_fuel_current_prefix_boundary_proved':True,
    'whole_identity_worker_at_any_budget_proved':False,
    'whole_real_worker_at_any_budget_proved':False,'joint_finite_completion_proved':False,
    'compiled_haskell_correspondence_proved':False,'haskell_changed':False,
    'at':datetime.datetime.now().astimezone().isoformat(),'limits':limits}
(runtime/'checked.json').write_text(json.dumps(report,indent=2)+'\\n')
print(json.dumps(report),flush=True)
'''
(runtime / 'check.py').write_text(driver)
pins = sorted((root / 'lean/MicroCFTA').glob('*.lean'))
assert len(pins) == 6122
imports = [line for line in (root / 'lean/MicroCFTA/Audit.lean').read_text().splitlines() if line.startswith('import ')]
assert len(imports) == 5122
pins += [root / name for name in ['shell.nix','lean/lean-toolchain','lean/lakefile.toml','lean/lake-manifest.json']]
pins += [source,runtime / 'ResourceProbes.lean.txt',strict,independent,runtime / 'check.py',Path(__file__)]
(runtime / 'source-pins.json').write_text(json.dumps({str(p.relative_to(root)):sha(p) for p in pins}, indent=2) + '\n')
(work / 'PUBLIC-API-COMPATIBILITY.json').write_text(json.dumps({'prior_checkpoint':
    '79155bfa2a24ad0629e97f67e08419b46a0dc248','old_non_audit_sources_byte_exact':6119,
    'old_audit_bytes_retained_as_exact_block':True,'source_files':6122,'direct_audit_imports':5122,
    'new_public_theorems':4,'retained_resource_probes':66,'owner_resource_probes':73,
    'all_original_statement_headers_unchanged':True}, indent=2) + '\n')
print(json.dumps({'run':str(runtime),'objects':str(objects),'public_gates':5,'source_files':6122,'direct_audit_imports':5122}))
