from pathlib import Path
import datetime
import hashlib
import json
import re
import subprocess

ROOT = Path('/home/tritlo/Code/mcfta')
BASE = ROOT/'lean/restart-evidence'
CONTROL = BASE/'20261118-worker-endpoint-seeds-step-source-commit-control-draft'
WORK = BASE/'20261118-worker-endpoint-seeds-step-work'
PARENT = '7e0d728d1a90bdd6f9150e031f27deea3eddb3b1'
SOURCE = '60824ae753b260f486726d256290f5ed683ff46c'
MESSAGE = 'Preserve growth and cache seeds through local worker steps'
SHA = lambda data: hashlib.sha256(data).hexdigest()
read = lambda path: json.loads(path.read_text())
GIT = lambda *args: subprocess.check_output(['git',*args],cwd=ROOT)
assert (CONTROL/'STATUS.txt').read_text().startswith('FROZEN'), 'OPEN control; do not execute.'
assert Path(__file__).resolve().parent == WORK.resolve()
assert Path(__file__).read_bytes() == (CONTROL/'commit-source.py').read_bytes()


def verify(path,record):
    data = path.read_bytes()
    assert SHA(data) == (record['sha256'] if isinstance(record,dict) else record),str(path)
    if isinstance(record,dict) and 'bytes' in record:
        assert len(data) == record['bytes'],str(path)
    return data


def records(value):
    if isinstance(value,list):
        return [(item.get('file',item.get('path')),item) for item in value]
    return records(value['files']) if 'files' in value else value.items()


manifest = read(CONTROL/'MANIFEST.json')
assert manifest['all_final_receipts_bound_before_freeze']
for name,record in records(manifest):
    verify(CONTROL/name,record)
for name,record in read(CONTROL/'SOURCE-PINS.json').items():
    verify(ROOT/name,record)
assert not (WORK/'SOURCE-COMMIT.json').exists()
stage = read(WORK/'SOURCES-NORMAL-STAGING.json')
assert stage['status'] == 'SOURCE_NORMAL_STAGING_COMPLETED' and stage['normal_Source_changed']
assert stage['source_baseline'] == SOURCE and stage['prior_checkpoint'] == PARENT
components = stage['components']
FILES = [c['source_path'] for c in components]+['lean/MicroCFTA/Audit.lean']
assert len(FILES) == len(set(FILES)) == 4 and set(FILES) == set(stage['exact_Source_write_paths']) == set(stage['baseline_overrides'])
assert stage['new_modules'] == 0 and stage['changed_existing_owners'] == 3
assert (stage['source_files'],stage['audit_imports'],stage['audit_reports'],stage['independent_reports']) == (6286,5286,746,341)
assert (stage['inherited_reports'],stage['fresh_public_reports'],stage['fresh_private_reports'],stage['combined_reports']) == (540,2,3,545)
assert stage['new_public_theorems'] == 2 and stage['new_private_theorems'] == 6
assert stage['new_private_reported_laws'] == stage['new_private_helpers_transitive'] == 3
assert stage['new_definitions'] == stage['definition_checks'] == stage['definition_axiom_credit'] == 0
assert stage['fresh_credit_for_old_owner_theorems'] == stage['rebuilt_Source65_leaf_and_zero_base_extra_credit'] == 0
push = read(ROOT/stage['prior_checkpoint_push_receipt'])
assert push['source_commit'] == SOURCE and push['checkpoint_commit'] == push['remote_commit'] == PARENT
assert push['actual_push_terminal'] and push['actual_remote_check_terminal']
assert push['actual_push_terminal_exit'] == push['actual_remote_check_terminal_exit'] == push['postpush_current_tree_verifier_terminal_exit'] == 0
baseline = json.loads(verify(ROOT/stage['source_baseline_path'],stage['source_baseline_sha256']))
assert len(baseline['sources']) == 6286 and len(baseline['toolchain']) == 4
assert set(baseline['sources']) == {str(path.relative_to(ROOT)) for path in (ROOT/'lean/MicroCFTA').glob('*.lean')}
assert len(set(baseline['sources'])-set(FILES)) == stage['old_other_Source_files_byte_exact'] == 6282
for name,record in {**baseline['sources'],**baseline['toolchain']}.items():
    verify(ROOT/stage['baseline_overrides'].get(name,name),record)
normal_pins = json.loads(verify(WORK/'NORMAL-SOURCE-PINS.json',stage['normal_source_pins_sha256']))
assert len(normal_pins) == 6290
for name,record in normal_pins.items():
    verify(ROOT/name,record)
stage_actual = read(WORK/'STAGING-ACTUAL-RUN.json')
assert stage_actual['actual_terminal'] and stage_actual['actual_terminal_exit'] == 0
assert stage_actual['exact_Source_write_paths'] == stage['exact_Source_write_paths'] and stage_actual['git_index_empty']
assert stage_actual['normal_source_pins_sha256'] == stage['normal_source_pins_sha256']
private,private_actual = read(WORK/'REPAIR-CHECK-VERIFIED.json'),read(WORK/'REPAIR-CHECK-ACTUAL-RUN.json')
assert private['actual_terminal'] and private_actual['actual_terminal'] and private['actual_terminal_exit'] == private_actual['actual_terminal_exit'] == 0
assert private['actual_session'] == private_actual['actual_session'] == stage['actual_private_session']
private_run = BASE/private['runtime']
private_checked = json.loads(verify(private_run/'checked.json',private['checked_sha256']))
assert private_checked == json.loads(verify(private_run/'results.json',private['results_sha256']))
assert private_checked['checks'] == private['checks'] and private_checked['proof_credit'] and private_checked['source_pins_unchanged']
assert [item['total_axiom_reports'] for item in private_checked['checks']] == [1,1,3]
private_pins = json.loads(verify(private_run/'source-pins.json',private['source_pins_sha256']))
assert len(private_pins) == private['pins_independently_reverified']
for name,record in private_pins.items():
    verify(ROOT/stage['baseline_overrides'].get(name,name),record)
rejected = read(WORK/'FIRST-CHECK-REJECTED.json')
failed = BASE/rejected['runtime']
assert rejected['actual_session'] == 21212 and rejected['actual_terminal'] and rejected['actual_terminal_exit'] == 1
assert not read(failed/'results.json')['proof_credit'] and not(failed/'checked.json').exists()
actual,verified = read(WORK/'PUBLICATION-ACTUAL-RUN.json'),read(WORK/'PUBLICATION-VERIFIED.json')
assert actual['actual_terminal'] and verified['actual_terminal'] and actual['actual_terminal_exit'] == verified['actual_terminal_exit'] == 0
assert actual['actual_session'] == verified['actual_session'] and type(verified['actual_session']) is int
assert actual['runtime'] == verified['runtime'] == '20261118-worker-endpoint-seeds-step-publication'
publication_control = BASE/'20261118-worker-endpoint-seeds-step-publication-control-draft'
assert actual['control_manifest_sha256'] == SHA((publication_control/'MANIFEST.json').read_bytes())
assert actual['preparer_sha256'] == SHA((publication_control/'prepare-publication.py').read_bytes()) and actual['preparer_terminal_exit'] == 0
publication = BASE/verified['runtime']
report = json.loads(verify(publication/'checked.json',verified['checked_sha256']))
assert report == json.loads(verify(publication/'results.json',verified['results_sha256'])) and report['checks'] == verified['checks']
assert report['all_five_gates_passed'] and report['source_pins_unchanged']
assert [item['total_axiom_reports'] for item in report['checks']] == [746,5,341,746,746]
assert all(item['declaration_checks'] == 0 and item['exit'] == 0 and not item['diagnostics'] and not item['sorryAx'] and not item['nonstandard_axioms'] for item in report['checks'])
assert report['checks'][1]['axiom_groups'] == sum(item['axiom_groups'] for item in private_checked['checks'])
assert report['checks'][1]['axiom_free_reports'] == sum(item['axiom_free_reports'] for item in private_checked['checks'])
assert (report['new_public_theorems'],report['new_private_theorems'],report['new_theorem_declarations']) == (2,6,8)
assert report['new_private_reported_laws'] == report['new_private_helpers_transitive'] == 3
assert report['new_definitions'] == report['definition_checks'] == report['definition_axiom_credit'] == 0
assert (report['inherited_reports'],report['fresh_reports'],report['combined_reports']) == (540,5,545)
assert type(report['audited_theorems']) is int and report['audited_theorems'] == verified['audited_theorems']
pub_pins = json.loads(verify(publication/'source-pins.json',verified['source_pins_sha256']))
assert len(pub_pins) == verified['pins_independently_reverified']
for name,record in pub_pins.items():
    verify(ROOT/name,record)
source_bytes = {}
for component in components:
    chosen = BASE/component['packet']
    current = verify(ROOT/component['source_path'],{'sha256':component['raw_sha256'],'bytes':component['raw_bytes']})
    assert current == (chosen/component['source']).read_bytes()
    old = verify(ROOT/stage['baseline_overrides'][component['source_path']],baseline['sources'][component['source_path']])
    assert len(old) == component['old_owner_bytes'] and component['old_owner_offset'] == 0 and current.startswith(old)
    for header in component['headers']:
        data = verify(BASE/header['packet']/header['file'],header['sha256']).rstrip()
        assert current.count(data) == 1 and re.match(rb'\s*:= by',current[current.index(data)+len(data):])
    source_bytes[component['source_path']] = current
old_audit = verify(ROOT/stage['baseline_overrides']['lean/MicroCFTA/Audit.lean'],baseline['sources']['lean/MicroCFTA/Audit.lean'])
public = (WORK/'PUBLIC-PROBES.lean.txt').read_bytes()
assert len(old_audit) == 436723 and public.count(b'#print axioms ') == 2 and b'#check ' not in public
source_bytes['lean/MicroCFTA/Audit.lean'] = old_audit+b'\n'+public
assert len(source_bytes['lean/MicroCFTA/Audit.lean']) == 436889
assert (ROOT/'lean/MicroCFTA/Audit.lean').read_bytes() == source_bytes['lean/MicroCFTA/Audit.lean']
assert len(re.findall(rb'^import ',source_bytes['lean/MicroCFTA/Audit.lean'],re.M)) == 5286
assert GIT('branch','--show-current').decode().strip() == 'formalize' and GIT('rev-parse','HEAD').decode().strip() == PARENT
assert not GIT('diff','--cached','--name-only') and set(GIT('diff','--name-only','HEAD').decode().splitlines()) == set(FILES)
assert set(GIT('ls-files','--',*FILES).decode().splitlines()) == set(FILES)
for name in FILES:
    assert GIT('show',PARENT+':'+name) == (ROOT/stage['baseline_overrides'][name]).read_bytes()
# Root stages only four existing tracked Source paths. No forced add is needed.
subprocess.run(['git','add','--',*FILES],cwd=ROOT,check=True)
assert set(GIT('diff','--cached','--name-only').decode().splitlines()) == set(FILES)
for name,data in source_bytes.items():
    assert GIT('show',':'+name) == data
subprocess.run(['git','diff','--cached','--check'],cwd=ROOT,check=True)
subprocess.run(['git','commit','--quiet','-m',MESSAGE],cwd=ROOT,check=True)
head = GIT('rev-parse','HEAD').decode().strip()
assert GIT('rev-parse',head+'^').decode().strip() == PARENT
assert set(GIT('diff-tree','--no-commit-id','--name-only','-r',head).decode().splitlines()) == set(FILES)
assert not GIT('status','--porcelain','--untracked-files=no')
for name,record in normal_pins.items():
    verify(ROOT/name,record)
receipt = dict(at=datetime.datetime.now().astimezone().isoformat(),source_commit=head,parent=PARENT,files=FILES,
    actual_terminal=True,actual_terminal_exit=0,message=MESSAGE,publication_actual_session=verified['actual_session'],
    audited_theorems=report['audited_theorems'],publication_pins_independently_reverified=verified['pins_independently_reverified'],
    source_files=6286,audit_imports=5286,audit_reports=746,independent_reports=341,new_public_theorems=2,new_private_theorems=6,
    new_private_reported_laws=3,new_private_helpers_transitive=3,new_theorem_declarations=8,new_definitions=0,
    explicit_definition_checks=0,definition_axiom_credit=0,fresh_public_reports=2,fresh_private_reports=3,inherited_reports=540,combined_reports=545,
    resource_reports_inherited=264,private_actual_session=private['actual_session'],rejected_private_actual_sessions=[21212],rejected_private_credit=0,
    old_owner_bytes=[10225,9058,2549042],old_owner_offset=0,old_audit_bytes=436723,old_audit_offset=0,other_old_Source_files_byte_exact=6282,
    selected_shared_FIRST_bytes_changed=True,original_selected_FIRST_successfully_elaborated=False,original_entire_candidate_prefix_equality_claimed=False,
    force_add_used=False,full_worker_endpoint_producer_proved=False,complete_eager_worker_query_log_proved=False,joint_finite_completion_proved=False,haskell_changed=False)
(WORK/'SOURCE-COMMIT.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))
