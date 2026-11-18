from pathlib import Path
import datetime
import hashlib
import json
import re
import subprocess

ROOT = Path('/home/tritlo/Code/mcfta')
BASE = ROOT/'lean/restart-evidence'
CONTROL = BASE/'20261118-worker-endpoint-seeds-zero-source-commit-control-draft'
WORK = BASE/'20261118-worker-endpoint-seeds-zero-work'
LEAF_WORK = BASE/'20261118-actual-source-child-query-seeds-work'
PARENT = '51ff371093cf387f351c1f30428b48d9f9cf25be'
SOURCE = '08bc975d5073bbc96129b8183245080650e677c4'
OWNER = 'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'
MESSAGE = 'Preserve cache seeds at actual worker child and zero-depth endpoints'
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
assert stage['exact_Source_write_paths'] == [OWNER] and set(stage['baseline_overrides']) == {OWNER}
assert not stage['Audit_changed'] and stage['new_modules'] == 0 and stage['changed_existing_owners'] == 1
assert (stage['source_files'],stage['audit_imports'],stage['audit_reports'],stage['independent_reports']) == (6286,5286,744,339)
assert (stage['inherited_reports'],stage['fresh_private_reports'],stage['combined_reports']) == (538,2,540)
assert stage['new_public_theorems'] == 0 and stage['new_private_theorems'] == 2
assert stage['new_private_Prop_definitions'] == stage['definition_checks'] == 3 and stage['definition_axiom_credit'] == 0
assert stage['fresh_credit_for_old_owner_theorems'] == stage['rebuilt_prior_leaf_extra_credit'] == 0
push = read(ROOT/stage['prior_checkpoint_push_receipt'])
assert push['source_commit'] == SOURCE and push['checkpoint_commit'] == push['remote_commit'] == PARENT
assert push['actual_push_terminal'] and push['actual_remote_check_terminal']
assert push['actual_push_terminal_exit'] == push['actual_remote_check_terminal_exit'] == push['postpush_current_tree_verifier_terminal_exit'] == 0
baseline = json.loads(verify(ROOT/stage['source_baseline_path'],stage['source_baseline_sha256']))
assert len(baseline['sources']) == 6286 and len(baseline['toolchain']) == 4
assert set(baseline['sources']) == {str(path.relative_to(ROOT)) for path in (ROOT/'lean/MicroCFTA').glob('*.lean')}
assert len(set(baseline['sources'])-{OWNER}) == stage['old_other_Source_files_byte_exact'] == 6285
for name,record in {**baseline['sources'],**baseline['toolchain']}.items():
    verify(ROOT/stage['baseline_overrides'].get(name,name),record)
normal_pins = json.loads(verify(WORK/'NORMAL-SOURCE-PINS.json',stage['normal_source_pins_sha256']))
assert len(normal_pins) == 6290
for name,record in normal_pins.items():
    verify(ROOT/name,record)
stage_actual = read(WORK/'STAGING-ACTUAL-RUN.json')
assert stage_actual['actual_terminal'] and stage_actual['actual_terminal_exit'] == 0
assert stage_actual['exact_Source_write_paths'] == [OWNER] and stage_actual['git_index_empty']
assert stage_actual['normal_source_pins_sha256'] == stage['normal_source_pins_sha256']
private_sessions,class_groups,class_free = [],0,0
for work,declarations in [(LEAF_WORK,0),(WORK,3)]:
    receipt,actual = read(work/'REPAIR-CHECK-VERIFIED.json'),read(work/'REPAIR-CHECK-ACTUAL-RUN.json')
    assert receipt['actual_terminal'] and actual['actual_terminal'] and receipt['actual_terminal_exit'] == actual['actual_terminal_exit'] == 0
    assert receipt['actual_session'] == actual['actual_session']
    runtime = BASE/receipt['runtime']
    checked = json.loads(verify(runtime/'checked.json',receipt['checked_sha256']))
    assert checked == json.loads(verify(runtime/'results.json',receipt['results_sha256'])) and checked['checks'] == receipt['checks']
    assert checked['proof_credit'] and checked['source_pins_unchanged'] and len(checked['checks']) == 1
    item = checked['checks'][0]
    assert item['exit'] == 0 and not item['diagnostics'] and not item['sorryAx'] and not item['nonstandard_axioms']
    assert item['total_axiom_reports'] == 1 and item['declaration_checks'] == declarations
    private_sessions.append(receipt['actual_session']);class_groups += item['axiom_groups'];class_free += item['axiom_free_reports']
    private_pins = json.loads(verify(runtime/'source-pins.json',receipt['source_pins_sha256']))
    assert len(private_pins) == receipt['pins_independently_reverified']
    for name,digest in private_pins.items():
        verify(ROOT/stage['baseline_overrides'].get(name,name),digest)
for work,session in [(LEAF_WORK,15463),(WORK,78387)]:
    rejected = read(work/'FIRST-CHECK-REJECTED.json')
    run = BASE/rejected['runtime'];result = read(run/'results.json')
    assert rejected['actual_session'] == session and rejected['actual_terminal'] and rejected['actual_terminal_exit'] == 1
    assert not result['proof_credit'] and result['credited_private_reports'] == 0 and not (run/'checked.json').exists()
assert stage['actual_private_sessions'] == private_sessions
preparer_rejected = read(WORK/'PUBLICATION-PREPARER-REJECTED.json')
assert preparer_rejected['actual_session'] == 84654 and preparer_rejected['actual_terminal_exit'] == 1
assert not preparer_rejected['runtime_created'] and not preparer_rejected['compiler_run'] and preparer_rejected['proof_credit'] == 0
actual,verified = read(WORK/'PUBLICATION-ACTUAL-RUN.json'),read(WORK/'PUBLICATION-VERIFIED.json')
assert actual['actual_terminal'] and verified['actual_terminal'] and actual['actual_terminal_exit'] == verified['actual_terminal_exit'] == 0
assert actual['actual_session'] == verified['actual_session'] and type(verified['actual_session']) is int
assert actual['runtime'] == verified['runtime'] == '20261118-worker-endpoint-seeds-zero-fixture-repair-publication'
publication_control = BASE/'20261118-worker-endpoint-seeds-zero-fixture-repair-publication-control-draft'
assert actual['control_manifest_sha256'] == SHA((publication_control/'MANIFEST.json').read_bytes())
assert actual['preparer_sha256'] == SHA((publication_control/'prepare-publication-fixture-repair.py').read_bytes()) and actual['preparer_terminal_exit'] == 0
publication = BASE/verified['runtime']
report = json.loads(verify(publication/'checked.json',verified['checked_sha256']))
assert report == json.loads(verify(publication/'results.json',verified['results_sha256'])) and report['checks'] == verified['checks']
assert report['all_five_gates_passed'] and report['source_pins_unchanged']
assert [item['total_axiom_reports'] for item in report['checks']] == [744,2,339,744,744]
assert [item['declaration_checks'] for item in report['checks']] == [0,3,0,0,0]
assert all(item['exit'] == 0 and not item['diagnostics'] and not item['sorryAx'] and not item['nonstandard_axioms'] for item in report['checks'])
assert report['checks'][1]['axiom_groups'] == class_groups and report['checks'][1]['axiom_free_reports'] == class_free
assert report['new_public_theorems'] == 0 and report['new_private_theorems'] == report['new_theorem_declarations'] == 2
assert report['new_private_Prop_definitions'] == report['definition_checks'] == 3 and report['definition_axiom_credit'] == 0
assert report['inherited_reports'] == 538 and report['fresh_private_reports'] == 2 and report['combined_reports'] == 540
assert type(report['audited_theorems']) is int and report['audited_theorems'] == verified['audited_theorems']
pub_pins = json.loads(verify(publication/'source-pins.json',verified['source_pins_sha256']))
assert len(pub_pins) == verified['pins_independently_reverified']
for name,record in pub_pins.items():
    verify(ROOT/name,record)
component = stage['components'][0];candidate = BASE/component['packet']
current = verify(ROOT/OWNER,{'sha256':component['raw_sha256'],'bytes':component['raw_bytes']})
assert current == (candidate/component['source']).read_bytes()
for filename,digest in component['headers'].items():
    header = verify(candidate/filename,digest).rstrip()
    assert current.count(header) == 1
    if filename == 'FIRST-HEADER.lean.txt':
        assert re.match(rb'\s*:= by',current[current.index(header)+len(header):])
leaf_header = component['retained_leaf_header']
assert current.count(verify(BASE/leaf_header['packet']/leaf_header['file'],leaf_header['sha256']).rstrip()) == 1
old = verify(ROOT/stage['baseline_overrides'][OWNER],baseline['sources'][OWNER])
assert len(old) == 2533565 and current[72:72+len(old)] == old
assert (ROOT/'lean/MicroCFTA/Audit.lean').read_bytes() == GIT('show',PARENT+':lean/MicroCFTA/Audit.lean')
assert GIT('branch','--show-current').decode().strip() == 'formalize' and GIT('rev-parse','HEAD').decode().strip() == PARENT
assert not GIT('diff','--cached','--name-only')
assert GIT('diff','--name-only','HEAD').decode().splitlines() == [OWNER]
assert GIT('ls-files','--',OWNER).decode().splitlines() == [OWNER] and GIT('show',PARENT+':'+OWNER) == old
# Root commits one tracked Source owner. No document, Audit, or new module is staged.
subprocess.run(['git','add','--',OWNER],cwd=ROOT,check=True)
assert GIT('diff','--cached','--name-only').decode().splitlines() == [OWNER] and GIT('show',':'+OWNER) == current
subprocess.run(['git','diff','--cached','--check'],cwd=ROOT,check=True)
subprocess.run(['git','commit','--quiet','-m',MESSAGE],cwd=ROOT,check=True)
head = GIT('rev-parse','HEAD').decode().strip()
assert GIT('rev-parse',head+'^').decode().strip() == PARENT
assert GIT('diff-tree','--no-commit-id','--name-only','-r',head).decode().splitlines() == [OWNER]
assert not GIT('status','--porcelain','--untracked-files=no')
for name,record in normal_pins.items():
    verify(ROOT/name,record)
receipt = dict(at=datetime.datetime.now().astimezone().isoformat(),source_commit=head,parent=PARENT,files=[OWNER],
    actual_terminal=True,actual_terminal_exit=0,message=MESSAGE,publication_actual_session=verified['actual_session'],
    audited_theorems=report['audited_theorems'],publication_pins_independently_reverified=verified['pins_independently_reverified'],
    source_files=6286,audit_imports=5286,audit_reports=744,independent_reports=339,new_public_theorems=0,new_private_theorems=2,
    new_private_Prop_definitions=3,new_definitions=3,explicit_definition_checks=3,definition_axiom_credit=0,
    fresh_private_reports=2,inherited_reports=538,combined_reports=540,resource_reports_inherited=264,
    private_actual_sessions=private_sessions,rejected_private_actual_sessions=[15463,78387],rejected_private_credit=0,
    rejected_preparer_actual_sessions=[84654],rejected_preparer_compiler_runs=0,
    old_owner_bytes=2533565,old_owner_offset=72,other_old_Source_files_byte_exact=6285,Audit_changed=False,force_add_used=False,
    original_zero_FIRST_bytes_changed=True,original_failed_zero_FIRST_successfully_elaborated=False,
    all_original_eager_worker_query_admissions_proved=False,original_eager_worker_all_calls_Seeds_propagation_proved=False,
    joint_finite_completion_proved=False,haskell_changed=False)
(WORK/'SOURCE-COMMIT.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))
