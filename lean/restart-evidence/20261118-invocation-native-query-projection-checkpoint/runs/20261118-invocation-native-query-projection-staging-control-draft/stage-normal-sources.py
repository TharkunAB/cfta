from pathlib import Path
import datetime
import hashlib
import json
import re
import subprocess

ROOT = Path('/home/tritlo/Code/mcfta')
BASE = ROOT/'lean/restart-evidence'
CONTROL = BASE/'20261118-invocation-native-query-projection-staging-control-draft'
WORK = BASE/'20261118-invocation-native-query-projection-work'
assert Path(__file__).resolve().parent == WORK.resolve()
assert Path(__file__).read_bytes() == (CONTROL/'stage-normal-sources.py').read_bytes()
assert not (WORK/'SOURCES-NORMAL-STAGING.json').exists()
SHA = lambda data: hashlib.sha256(data).hexdigest()
read = lambda path: json.loads(path.read_text())
bound = set()


def verify(path, record):
    data = path.read_bytes()
    assert SHA(data) == (record['sha256']if isinstance(record,dict)else record),str(path)
    if isinstance(record,dict)and 'bytes'in record:
        assert len(data) == record['bytes'],str(path)
    bound.add(path)
    return data


def records(value):
    if isinstance(value,list):
        return [(entry.get('file',entry.get('path')),entry)for entry in value]
    if 'files'in value:
        return records(value['files'])
    if 'pins'in value:
        return records(value['pins'])
    return value.items()


def packet_files(packet, digest):
    manifest = json.loads(verify(packet/'MANIFEST.json',digest))
    for name,record in records(manifest['files']):
        verify(packet/name,record)


for name,record in records(read(CONTROL/'MANIFEST.json')['files']):
    verify(CONTROL/name,record)
bound.add(CONTROL/'MANIFEST.json')
for name,record in records(read(CONTROL/'RECEIPT-PINS.json')):
    verify(ROOT/name,record)
stage = read(CONTROL/'EXPECTED-STAGE.json')
assert stage['source_baseline'] == read(BASE/'20261118-child-dispatch-query-seeds-work/SOURCE-COMMIT.json')['source_commit']
assert (stage['source_files'],stage['audit_imports'],stage['audit_reports'],stage['independent_reports']) == (6286,5286,744,339)
assert (stage['fresh_reports'],stage['inherited_reports'],stage['combined_reports']) == (1,537,538)
assert stage['new_public_theorems'] == 1 and stage['new_projection_definitions'] == stage['new_definitions'] == 1
assert stage['new_private_helpers_transitive'] == stage['explicit_private_reports'] == stage['new_Prop_definitions'] == 0
assert stage['definition_checks'] == 1 and stage['definition_axiom_credit'] == 0
assert stage['resource_reports_inherited'] == 264 and stage['fresh_credit_for_old_owner_theorems'] == 0
prior = BASE/'20261118-child-dispatch-query-seeds-work'
publication = BASE/'20261118-child-dispatch-query-seeds-publication'
commit,commit_actual = read(prior/'SOURCE-COMMIT.json'),read(prior/'SOURCE-COMMIT-ACTUAL-RUN.json')
pub_verified,pub_actual = read(prior/'PUBLICATION-VERIFIED.json'),read(prior/'PUBLICATION-ACTUAL-RUN.json')
published = read(publication/'checked.json')
assert commit['source_commit'] == commit_actual['source_commit'] == stage['source_baseline']
assert commit['actual_terminal']and commit_actual['actual_terminal']
assert commit['actual_terminal_exit'] == commit_actual['actual_terminal_exit'] == 0
assert pub_verified['actual_session'] == pub_actual['actual_session'] == commit['publication_actual_session'] == 72804
assert pub_verified['actual_terminal']and pub_actual['actual_terminal']
assert pub_verified['actual_terminal_exit'] == pub_actual['actual_terminal_exit'] == 0
assert published == read(publication/'results.json')and pub_verified['checks'] == published['checks']
assert [entry['total_axiom_reports']for entry in published['checks']] == [743,2,338,743,743]
assert all(entry['exit'] == 0 and not entry['diagnostics']and not entry['sorryAx']and not entry['nonstandard_axioms']
    and entry['declaration_checks'] == (1 if index == 1 else 0) for index,entry in enumerate(published['checks']))
assert published['all_five_gates_passed']and published['source_pins_unchanged']
assert SHA((publication/'checked.json').read_bytes()) == pub_verified['checked_sha256']
pub_pins = json.loads(verify(publication/'source-pins.json',pub_verified['source_pins_sha256']))
assert len(pub_pins) == pub_verified['pins_independently_reverified']
for name,record in pub_pins.items():
    verify(ROOT/name,record)
push = read(ROOT/stage['prior_checkpoint_push_receipt'])
assert push['source_commit'] == stage['source_baseline']
assert push['checkpoint_commit'] == push['remote_commit'] == stage['prior_checkpoint']
assert push['actual_push_terminal']and push['actual_remote_check_terminal']
assert push['actual_push_terminal_exit'] == push['actual_remote_check_terminal_exit'] == push['postpush_current_tree_verifier_terminal_exit'] == 0
assert push['normal_Source_files'] == 6285
assert subprocess.check_output(['git','branch','--show-current'],cwd=ROOT).decode().strip() == 'formalize'
subprocess.run(['git','merge-base','--is-ancestor',stage['source_baseline'],'HEAD'],cwd=ROOT,check=True)
changes = subprocess.check_output(['git','diff','--name-only',stage['source_baseline'],'HEAD'],cwd=ROOT).decode().splitlines()
assert all(name in ['NEXT-PROMPT.md','HANDOFF.md','FINDINGS.md']or name.startswith('lean/restart-evidence/')for name in changes)
subprocess.run(['git','diff','--quiet',stage['source_baseline'],'HEAD','--','lean/MicroCFTA',
    'shell.nix','lean/lean-toolchain','lean/lakefile.toml','lean/lake-manifest.json'],cwd=ROOT,check=True)
assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=ROOT)
baseline = json.loads(verify(ROOT/stage['source_baseline_path'],stage['source_baseline_sha256']))
assert len(baseline['sources']) == 6285 and len(baseline['toolchain']) == 4
assert {str(path.relative_to(ROOT))for path in (ROOT/'lean/MicroCFTA').glob('*.lean')} == set(baseline['sources'])
for name,record in {**baseline['sources'],**baseline['toolchain']}.items():
    verify(ROOT/name,record)
    assert pub_pins[name] == record['sha256']
private = read(CONTROL/'PRIVATE-CHECK.json')
verified,actual = read(ROOT/private['verified_receipt']),read(ROOT/private['actual_receipt'])
runtime = BASE/private['runtime']
checked = json.loads(verify(runtime/'checked.json',verified['checked_sha256']))
assert checked == json.loads(verify(runtime/'results.json',verified['results_sha256']))
assert verified['actual_session'] == actual['actual_session'] == private['actual_session']
assert verified['actual_terminal']and actual['actual_terminal']
assert verified['actual_terminal_exit'] == actual['actual_terminal_exit'] == 0
assert verified['checks'] == checked['checks']and verified['proof_credit']and verified['source_pins_unchanged']
assert len(checked['checks']) == 1
check = checked['checks'][0]
assert check['total_axiom_reports'] == 1 and check['declaration_checks'] == 1
assert check['exit'] == 0 and not check['diagnostics']and not check['sorryAx']and not check['nonstandard_axioms']
assert check['axiom_groups'] == private['axiom_groups']and check['axiom_free_reports'] == private['axiom_free_reports']
assert checked['definition_axiom_credit'] == 0 and checked['new_private_helpers_transitive'] == 0
assert checked['limits'] == {'memory.max':'8589934592','memory.high':'8589934592','memory.swap.max':'0'}
pins = json.loads(verify(runtime/'source-pins.json',verified['source_pins_sha256']))
assert len(pins) == verified['pins_independently_reverified'] == private['pins']
for name,record in pins.items():
    verify(ROOT/name,record)
private_control = BASE/private['control']
packet_files(private_control,private['control_manifest_sha256'])
assert verified['selected_control'] == actual['selected_control'] == private['control']
assert verified['selected_control_manifest_sha256'] == actual['selected_control_manifest_sha256'] == private['control_manifest_sha256']
for rejected in stage['rejected_checks']:
    failed_receipt = read(ROOT/rejected['receipt'])
    failed_run = BASE/rejected['runtime']
    failed = json.loads(verify(failed_run/'results.json',failed_receipt['results_sha256']))
    assert failed_receipt['actual_session'] == rejected['actual_session']
    assert failed_receipt['actual_terminal']and failed_receipt['actual_terminal_exit'] == 1
    assert not failed['proof_credit']and failed['credited_public_reports'] == 0 and not (failed_run/'checked.json').exists()
    assert failed['checks'] == failed_receipt['checks']
    assert sum(entry['diagnostics']for entry in failed['checks']) == rejected['diagnostics']
    assert any(entry['sorryAx']for entry in failed['checks']) == rejected['sorryAx']
    failed_pins = json.loads(verify(failed_run/'source-pins.json',failed_receipt['source_pins_sha256']))
    assert len(failed_pins) == failed_receipt['pins_independently_reverified'] == rejected['pins']
    for name,record in failed_pins.items():
        verify(ROOT/name,record)
    packet_files(BASE/rejected['control'],rejected['control_manifest_sha256'])
components = read(CONTROL/'COMPONENTS.json')['components']
assert components == stage['components']and len(components) == 1
component = components[0]
selected = read(private_control/'SELECTION.json')['components'][0]
for key in ['module','packet','manifest_sha256','source','raw_sha256','raw_bytes','probe','probe_sha256','public_qnames','expected_axiom_reports','expected_declaration_checks','definition_qname','headers']:
    assert component[key] == selected[key],key
assert stage['compile_order'] == [component['module']]
packet = BASE/component['packet']
packet_files(packet,component['manifest_sha256'])
for filename in ['SOURCE-PINS.json','ADDITIONAL-SOURCE-PINS.json','DEPENDENCY-PINS.json']:
    if (packet/filename).exists():
        for name,record in records(read(packet/filename)):
            verify(ROOT/name,record)
raw = verify(packet/component['source'],{'sha256':component['raw_sha256'],'bytes':component['raw_bytes']})
assert not (ROOT/component['source_path']).exists(), 'The projection is a new normal module.'
for filename,digest in component['headers'].items():
    header = verify(packet/filename,digest).rstrip()
    assert raw.count(header) == 1 and re.match(rb'\s*:=',raw[raw.index(header)+len(header):])
assert len(re.findall(rb'^theorem ',raw,re.M)) == 1 and len(re.findall(rb'^noncomputable def ',raw,re.M)) == 1
assert not re.search(rb'^private theorem |set_option\s+(maxHeartbeats|maxRecDepth|warningAsError|linter\.)',raw,re.M)
public = verify(packet/component['public_probe'],component['public_probe_sha256'])
definition = verify(packet/component['definition_probe'],component['definition_probe_sha256'])
combined = verify(packet/component['probe'],component['probe_sha256'])
assert definition == ('#check '+component['definition_qname']+'\n').encode()
assert definition.count(b'#check ') == 1 and b'#print axioms 'not in definition
assert combined == definition+public
assert public.count(b'#print axioms ') == 1 and b'#check 'not in public
assert re.findall(r'^#print axioms (\S+)',public.decode(),re.M) == component['public_qnames']
assert (runtime/'source/MicroCFTA'/component['source']).read_bytes() == raw+b'\n'+combined
normal = {path.stem:path for path in (ROOT/'lean/MicroCFTA').glob('*.lean')}
active,seen,order,graph = [],set(),[],{}


def visit(name):
    assert name not in active,name
    if name in seen:
        return
    active.append(name)
    text = raw.decode()if name == component['module']else normal[name].read_text()
    graph[name] = re.findall(r'^import MicroCFTA\.([A-Za-z0-9_]+)\s*$',text,re.M)
    for dependency in graph[name]:
        visit(dependency)
    active.pop()
    seen.add(name)
    order.append(name)


visit(component['module'])
topology = read(CONTROL/'TOPOLOGICAL-ORDER.json')
assert graph == topology['direct_imports']and order == topology['full_transitive_order']
audit_path = ROOT/'lean/MicroCFTA/Audit.lean'
old_audit = verify(audit_path,{'sha256':stage['old_audit_sha256'],'bytes':436549})
assert old_audit == (CONTROL/'AUDIT-BEFORE.lean.txt').read_bytes()
imports = verify(CONTROL/'IMPORTS.lean.txt',stage['audit_import_prefix_sha256'])
assert imports == ('import MicroCFTA.'+component['module']+'\n').encode()and len(imports) == 73
assert imports not in old_audit
assert public == (CONTROL/'PUBLIC-PROBES.lean.txt').read_bytes()
assert definition == (CONTROL/'DEFINITION-CHECK.lean.txt').read_bytes()
new_audit = imports+old_audit+b'\n'+public
assert SHA(new_audit) == stage['staged_audit_sha256']and len(new_audit) == stage['staged_audit_bytes'] == 436723
assert new_audit[73:73+436549] == old_audit
assert len(re.findall(rb'^import ',new_audit,re.M)) == 5286
assert len(re.findall(rb'^#print axioms ',old_audit,re.M)) == 743 and len(re.findall(rb'^#print axioms ',new_audit,re.M)) == 744
assert definition not in new_audit
expected = json.loads(verify(CONTROL/'EXPECTED-NORMAL-SOURCE-PINS.json',stage['expected_normal_source_pins_sha256']))
assert len(expected) == 6290
assert set(stage['exact_Source_write_paths']) == {component['source_path'],'lean/MicroCFTA/Audit.lean'}
assert set(stage['baseline_overrides']) == {'lean/MicroCFTA/Audit.lean'}
assert stage['old_other_Source_files_byte_exact'] == 6284 and stage['new_modules'] == 1
snapshot = ROOT/stage['baseline_overrides']['lean/MicroCFTA/Audit.lean']
assert not snapshot.exists()
assert all(not(WORK/name).exists()for name in ['IMPORTS.lean.txt','PUBLIC-PROBES.lean.txt','DEFINITION-CHECK.lean.txt','NORMAL-SOURCE-PINS.json'])
for name,record in {**baseline['sources'],**baseline['toolchain']}.items():
    assert expected[name] == (SHA(new_audit)if name == 'lean/MicroCFTA/Audit.lean'else record['sha256'])
assert expected[component['source_path']] == SHA(raw)
bound.add(Path(__file__))
preflight_pins = {str(path.relative_to(ROOT)):SHA(path.read_bytes())for path in bound}
for name,digest in preflight_pins.items():
    assert SHA((ROOT/name).read_bytes()) == digest,name
# Only Root executes the following two normal Source writes after all gates pass.
snapshot.write_bytes(old_audit)
(ROOT/component['source_path']).write_bytes(raw)
audit_path.write_bytes(new_audit)
assert len(list((ROOT/'lean/MicroCFTA').glob('*.lean'))) == 6286
for name,digest in expected.items():
    assert SHA((ROOT/name).read_bytes()) == digest,name
for name,digest in preflight_pins.items():
    assert SHA((ROOT/stage['baseline_overrides'].get(name,name)).read_bytes()) == digest,name
for filename in ['IMPORTS.lean.txt','PUBLIC-PROBES.lean.txt','DEFINITION-CHECK.lean.txt']:
    (WORK/filename).write_bytes((CONTROL/filename).read_bytes())
(WORK/'NORMAL-SOURCE-PINS.json').write_bytes((CONTROL/'EXPECTED-NORMAL-SOURCE-PINS.json').read_bytes())
actual_stage = dict(stage)
actual_stage.update(status='SOURCE_NORMAL_STAGING_COMPLETED',staged_at=datetime.datetime.now().astimezone().isoformat(),
    actual_private_session=private['actual_session'],normal_Source_changed=True,published=False,
    actual_Source_files=6286,actual_audit_imports=5286,actual_audit_reports=744,
    prior_source_checkpoint_push_verified=True,normal_source_pins_sha256=SHA((WORK/'NORMAL-SOURCE-PINS.json').read_bytes()))
(WORK/'SOURCES-NORMAL-STAGING.json').write_text(json.dumps(actual_stage,indent=2)+'\n')
print(json.dumps(actual_stage,indent=2))
