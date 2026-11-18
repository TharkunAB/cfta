from pathlib import Path
import datetime
import hashlib
import json
import re
import subprocess

ROOT = Path('/home/tritlo/Code/mcfta')
BASE = ROOT/'lean/restart-evidence'
CONTROL = BASE/'20261118-worker-current-seeds-source-commit-control-draft'
STAGE_CONTROL = BASE/'20261118-worker-current-seeds-staging-control-draft'
PUBLICATION_CONTROL = BASE/'20261118-worker-current-seeds-publication-control-draft'
WORK = BASE/'20261118-worker-inner-selected-prefix-seeds-work'
PARENT = '396cbe25170c4d2be9834f4cefcf99a25f500bb8'
SOURCE = '0647287cb3a886b10f8455be850609a3735f9e31'
OWNER = 'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'
FILES = [OWNER]
MESSAGE = 'Preserve source cache seeds through eager worker recursion'
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
assert stage['exact_Source_write_paths'] == FILES and set(stage['baseline_overrides']) == {OWNER}
assert stage['new_modules'] == 0 and stage['changed_existing_owners'] == 1 and not stage['Audit_changed']
assert (stage['source_files'],stage['audit_imports'],stage['audit_reports'],stage['independent_reports']) == (6286,5286,746,341)
assert (stage['inherited_reports'],stage['fresh_public_reports'],stage['fresh_private_reports'],stage['combined_reports']) == (545,0,15,560)
assert stage['new_public_theorems'] == 0 and stage['new_private_theorems'] == 15 and stage['new_private_helpers_transitive'] == 0
assert stage['new_definitions'] == stage['definition_checks'] == stage['definition_axiom_credit'] == 0
assert stage['fresh_credit_for_old_owner_theorems'] == stage['rebuilt_Source66_steps_extra_credit'] == 0
push = read(ROOT/stage['prior_checkpoint_push_receipt'])
assert push['source_commit'] == SOURCE and push['checkpoint_commit'] == push['remote_commit'] == PARENT
assert push['actual_push_terminal'] and push['actual_remote_check_terminal']
assert push['actual_push_terminal_exit'] == push['actual_remote_check_terminal_exit'] == push['postpush_current_tree_verifier_terminal_exit'] == 0
baseline = json.loads(verify(ROOT/stage['source_baseline_path'],stage['source_baseline_sha256']))
assert len(baseline['sources']) == 6286 and len(baseline['toolchain']) == 4
assert set(baseline['sources']) == {str(p.relative_to(ROOT)) for p in (ROOT/'lean/MicroCFTA').glob('*.lean')}
assert len(set(baseline['sources'])-{OWNER}) == stage['old_other_Source_files_byte_exact'] == 6285
for name,record in {**baseline['sources'],**baseline['toolchain']}.items():
    verify(ROOT/stage['baseline_overrides'].get(name,name),record)
normal_pins = json.loads(verify(WORK/'NORMAL-SOURCE-PINS.json',stage['normal_source_pins_sha256']))
assert len(normal_pins) == 6290
for name,record in normal_pins.items():
    verify(ROOT/name,record)
actual_stage = read(WORK/'STAGING-ACTUAL-RUN.json')
assert actual_stage['actual_terminal'] and actual_stage['actual_terminal_exit'] == 0
assert actual_stage['exact_Source_write_paths'] == FILES and actual_stage['git_index_empty']
assert actual_stage['normal_source_pins_sha256'] == stage['normal_source_pins_sha256']
subset_records = read(STAGE_CONTROL/'PRIVATE-SUBSETS.json')['subsets']
private_reports,private_sessions,groups,free = [],[],0,0
for subset in subset_records:
    verified,actual = read(BASE/subset['work']/subset['verified']),read(BASE/subset['work']/subset['actual'])
    assert verified['actual_terminal'] and actual['actual_terminal'] and verified['actual_terminal_exit'] == actual['actual_terminal_exit'] == 0
    assert verified['actual_session'] == actual['actual_session']
    runtime = BASE/verified['runtime']
    checked = json.loads(verify(runtime/'checked.json',verified['checked_sha256']))
    assert checked == json.loads(verify(runtime/'results.json',verified['results_sha256']))
    assert checked['checks'] == verified['checks'] and checked['proof_credit'] and checked['source_pins_unchanged']
    assert len(checked['checks']) == 1
    item = checked['checks'][0]
    assert item['exit'] == 0 and not item['diagnostics'] and not item['sorryAx'] and not item['nonstandard_axioms']
    assert item['total_axiom_reports'] == subset['reports'] and item['declaration_checks'] == 0
    pp = json.loads(verify(runtime/'source-pins.json',verified['source_pins_sha256']))
    assert len(pp) == verified['pins_independently_reverified']
    for name,record in pp.items():
        verify(ROOT/stage['baseline_overrides'].get(name,name),record)
    private_reports.append(subset['reports']);private_sessions.append(verified['actual_session'])
    groups += item['axiom_groups'];free += item['axiom_free_reports']
assert private_reports == [4,11] and private_sessions == stage['actual_private_sessions'] and groups+free == 15
for rejected_entry in read(STAGE_CONTROL/'REJECTED-CHECKS.json'):
    rejected = read(ROOT/rejected_entry['receipt'])
    assert rejected['actual_terminal'] and rejected['actual_terminal_exit'] == 1
    assert rejected['actual_session'] == rejected_entry['actual_session']
    assert not rejected['proof_credit'] and rejected['credited_public_reports'] == rejected['credited_private_reports'] == 0
focused = read(WORK/'FOCUSED-SUBCHECKS.json')
assert focused['whole_fixed_batch_credit'] == 0 and [e['actual_session'] for e in focused['runs']] == [54647,31662,95539,26176]
assert all(e['whole_fixed_batch_proof_credit'] == 0 for e in focused['runs'])
actual,verified = read(WORK/'PUBLICATION-ACTUAL-RUN.json'),read(WORK/'PUBLICATION-VERIFIED.json')
assert actual['actual_terminal'] and verified['actual_terminal'] and actual['actual_terminal_exit'] == verified['actual_terminal_exit'] == 0
assert actual['actual_session'] == verified['actual_session'] and type(verified['actual_session']) is int
assert actual['runtime'] == verified['runtime'] == '20261118-worker-current-seeds-publication'
assert actual['control_manifest_sha256'] == SHA((PUBLICATION_CONTROL/'MANIFEST.json').read_bytes())
assert actual['preparer_sha256'] == SHA((PUBLICATION_CONTROL/'prepare-publication.py').read_bytes()) and actual['preparer_terminal_exit'] == 0
runtime = BASE/verified['runtime']
report = json.loads(verify(runtime/'checked.json',verified['checked_sha256']))
assert report == json.loads(verify(runtime/'results.json',verified['results_sha256'])) and report['checks'] == verified['checks']
assert report['all_five_gates_passed'] and report['source_pins_unchanged']
assert [item['total_axiom_reports'] for item in report['checks']] == [746,15,341,746,746]
assert all(item['exit'] == 0 and not item['diagnostics'] and not item['sorryAx'] and not item['nonstandard_axioms'] and item['declaration_checks'] == 0 for item in report['checks'])
assert report['checks'][1]['axiom_groups'] == groups and report['checks'][1]['axiom_free_reports'] == free
assert (report['new_public_theorems'],report['new_private_theorems'],report['new_private_helpers_transitive'],report['new_definitions']) == (0,15,0,0)
assert report['definition_checks'] == report['definition_axiom_credit'] == 0
assert (report['inherited_reports'],report['fresh_reports'],report['combined_reports']) == (545,15,560)
assert type(report['audited_theorems']) is int and report['audited_theorems'] == verified['audited_theorems']
pp = json.loads(verify(runtime/'source-pins.json',verified['source_pins_sha256']))
assert len(pp) == verified['pins_independently_reverified']
for name,record in pp.items():
    verify(ROOT/name,record)
component = stage['component'];chosen = BASE/component['packet']
raw = verify(ROOT/OWNER,{'bytes':component['raw_bytes'],'sha256':component['raw_sha256']})
assert raw == (chosen/component['source']).read_bytes()
old = verify(ROOT/stage['baseline_overrides'][OWNER],baseline['sources'][OWNER])
assert len(old) == component['old_owner_bytes'] == 2576264 and component['old_owner_offset'] == 137 and raw[137:137+len(old)] == old
fixed = verify(BASE/component['fixed_packet']/component['source'],{'bytes':component['fixed_raw_bytes'],'sha256':component['fixed_raw_sha256']})
assert raw[68:68+len(fixed)] == fixed
for header in component['headers']:
    data = verify(BASE/header['packet']/header['file'],header['sha256']).rstrip()
    assert raw.count(data) == 1 and re.match(rb'\s*:= by',raw[raw.index(data)+len(data):])
assert len(component['headers']) == len(component['private_qnames']) == 15
assert (ROOT/'lean/MicroCFTA/Audit.lean').read_bytes() == verify(ROOT/'lean/MicroCFTA/Audit.lean',baseline['sources']['lean/MicroCFTA/Audit.lean'])
assert len((ROOT/'lean/MicroCFTA/Audit.lean').read_bytes()) == 436889
assert GIT('branch','--show-current').decode().strip() == 'formalize' and GIT('rev-parse','HEAD').decode().strip() == PARENT
assert not GIT('diff','--cached','--name-only') and set(GIT('diff','--name-only','HEAD').decode().splitlines()) == {OWNER}
assert GIT('ls-files','--',OWNER).decode().splitlines() == FILES
assert GIT('show',PARENT+':'+OWNER) == old
# Root stages the sole existing owner. Audit, documents, artifacts and caches are excluded.
subprocess.run(['git','add','--',OWNER],cwd=ROOT,check=True)
assert GIT('diff','--cached','--name-only').decode().splitlines() == FILES and GIT('show',':'+OWNER) == raw
subprocess.run(['git','diff','--cached','--check'],cwd=ROOT,check=True)
subprocess.run(['git','commit','--quiet','-m',MESSAGE],cwd=ROOT,check=True)
head = GIT('rev-parse','HEAD').decode().strip()
assert GIT('rev-parse',head+'^').decode().strip() == PARENT
assert GIT('diff-tree','--no-commit-id','--name-only','-r',head).decode().splitlines() == FILES
assert not GIT('status','--porcelain','--untracked-files=no')
for name,record in normal_pins.items():
    verify(ROOT/name,record)
receipt = dict(at=datetime.datetime.now().astimezone().isoformat(),source_commit=head,parent=PARENT,files=FILES,
    actual_terminal=True,actual_terminal_exit=0,message=MESSAGE,publication_actual_session=verified['actual_session'],
    audited_theorems=report['audited_theorems'],publication_pins_independently_reverified=verified['pins_independently_reverified'],
    source_files=6286,audit_imports=5286,audit_reports=746,independent_reports=341,new_public_theorems=0,new_private_theorems=15,
    new_private_helpers_transitive=0,new_definitions=0,explicit_definition_checks=0,definition_axiom_credit=0,
    fresh_public_reports=0,fresh_private_reports=15,inherited_reports=545,combined_reports=560,resource_reports_inherited=264,
    private_actual_sessions=private_sessions,rejected_private_actual_sessions=[e['actual_session'] for e in read(STAGE_CONTROL/'REJECTED-CHECKS.json')],rejected_private_credit=0,
    focused_actual_sessions=[54647,31662,95539,26176],focused_extra_publication_credit=0,
    old_owner_bytes=2576264,old_owner_offset=137,old_Audit_bytes=436889,Audit_changed=False,other_old_Source_files_byte_exact=6285,
    fourteen_original_FIRSTs_byte_exact=True,scan_FIRST_bytes_changed=True,original_scan_FIRST_successfully_elaborated=False,old_entire927_owner_prefix_exact=False,force_add_used=False,
    complete_eager_worker_query_log_proved=False,joint_finite_completion_proved=False,haskell_changed=False)
(WORK/'SOURCE-COMMIT.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))
