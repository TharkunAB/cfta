from pathlib import Path
import datetime
import hashlib
import json
import subprocess
ROOT = Path('/home/tritlo/Code/mcfta')
BASE = ROOT/'lean/restart-evidence'
CONTROL = BASE/'20261118-source-entry-endpoint-seeds-source-commit-control-draft'
PUBLICATION_CONTROL = BASE/'20261118-source-entry-endpoint-seeds-import-repair-publication-control-draft'
WORK = BASE/'20261118-source-entry-endpoint-seeds-work'
RUNTIME = BASE/'20261118-source-entry-endpoint-seeds-import-repair-publication'
PARENT = 'e54bd1879c3ab2c01c4815ec0f81b87533b7ca32'
OWNER = 'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'
COLD = 'lean/MicroCFTA/SourceCurrentAllocatedPartialInitialSeeds.lean'
AUDIT = 'lean/MicroCFTA/Audit.lean'
FILES = [OWNER,COLD,AUDIT]
MESSAGE = 'Expose source cache seed preservation at eager endpoints'
SHA = lambda data: hashlib.sha256(data).hexdigest()
read = lambda path: json.loads(path.read_text())
GIT = lambda *args: subprocess.check_output(['git',*args],cwd=ROOT)
assert (CONTROL/'STATUS.txt').read_text().startswith('FROZEN'),'OPEN control; do not execute.'
assert Path(__file__).resolve().parent == WORK.resolve() and Path(__file__).read_bytes() == (CONTROL/'commit-source.py').read_bytes()
assert read(CONTROL/'MANIFEST.json')['all_final_receipts_bound_before_freeze']
assert not (WORK/'SOURCE-COMMIT.json').exists()
stage = read(WORK/'SOURCES-NORMAL-STAGING.json')
OVERRIDES = stage['baseline_overrides']
exec(compile((PUBLICATION_CONTROL/'validate-inputs.py.txt').read_text(),str(PUBLICATION_CONTROL/'validate-inputs.py.txt'),'exec'))
packet(CONTROL)
for name,record in records(read(CONTROL/'SOURCE-PINS.json')):
    verify(ROOT/name,record)
stage,baseline,components,raws,probes,audit,private,prior,classification = preflight(PUBLICATION_CONTROL)
assert stage['status'] == 'SOURCE_NORMAL_STAGING_COMPLETED' and set(stage['exact_Source_write_paths']) == set(FILES)
actual_stage = read(WORK/'STAGING-ACTUAL-RUN.json')
assert actual_stage['actual_terminal'] and actual_stage['actual_terminal_exit'] == 0 and actual_stage['git_index_empty']
verified,actual = read(WORK/'IMPORT-REPAIR-PUBLICATION-VERIFIED.json'),read(WORK/'IMPORT-REPAIR-PUBLICATION-ACTUAL-RUN.json')
assert verified['actual_terminal'] and actual['actual_terminal'] and verified['actual_terminal_exit'] == actual['actual_terminal_exit'] == 0
assert type(verified['actual_session']) is int and verified['actual_session'] == actual['actual_session']
assert verified['runtime'] == actual['runtime'] == RUNTIME.name
assert actual['control_manifest_sha256'] == SHA((PUBLICATION_CONTROL/'MANIFEST.json').read_bytes())
assert actual['preparer_sha256'] == SHA((PUBLICATION_CONTROL/'prepare-import-repair-publication.py').read_bytes()) and actual['preparer_terminal_exit'] == 0
report = json.loads(verify(RUNTIME/'checked.json',verified['checked_sha256']))
assert report == json.loads(verify(RUNTIME/'results.json',verified['results_sha256'])) and report['checks'] == verified['checks']
assert report['all_five_gates_passed'] and report['source_pins_unchanged']
assert [e['total_axiom_reports']for e in report['checks']] == [748,3,343,748,748]
assert all(e['exit'] == 0 and not e['diagnostics'] and not e['sorryAx'] and not e['nonstandard_axioms'] and e['declaration_checks'] == 0 for e in report['checks'])
assert report['checks'][1]['axiom_groups'] == classification['axiom_groups'] and report['checks'][1]['axiom_free_reports'] == classification['axiom_free_reports']
assert (report['fresh_public_reports'],report['fresh_private_reports'],report['inherited_reports'],report['combined_reports']) == (2,1,560,563)
assert report['new_definitions'] == report['definition_checks'] == report['definition_axiom_credit'] == report['new_private_helpers_transitive'] == 0
assert type(report['audited_theorems']) is int and report['audited_theorems'] == verified['audited_theorems']
pub_pins = json.loads(verify(RUNTIME/'source-pins.json',verified['source_pins_sha256']))
assert len(pub_pins) == verified['pins_independently_reverified']
for name,record in pub_pins.items():
    verify(ROOT/name,record)
for entry in read(CONTROL/'rejected-publications.json'):
    rejected = read(ROOT/entry['receipt'])
    rejected_actual = read(ROOT/entry['actual_receipt'])
    assert rejected['actual_session'] == rejected_actual['actual_session'] == entry['actual_session']
    assert rejected['actual_terminal'] and rejected_actual['actual_terminal'] and rejected['actual_terminal_exit'] == rejected_actual['actual_terminal_exit'] == 1
    assert not rejected['proof_credit'] and rejected['credited_public_reports'] == rejected['credited_private_reports'] == 0
    failed_run = BASE/entry['runtime']
    assert not (failed_run/'checked.json').exists()
    failed = json.loads(verify(failed_run/'results.json',rejected['results_sha256']))
    assert failed['checks'] == rejected['checks']
    failed_pins = json.loads(verify(failed_run/'source-pins.json',rejected['source_pins_sha256']))
    assert len(failed_pins) == rejected['pins_independently_reverified'] == entry['pins']
    for name,record in failed_pins.items():
        verify(ROOT/name,record)
normal = json.loads(verify(WORK/'NORMAL-SOURCE-PINS.json',stage['normal_source_pins_sha256']))
assert len(normal) == 6291 and len(list((ROOT/'lean/MicroCFTA').glob('*.lean'))) == 6287
for name,digest in normal.items():
    verify(ROOT/name,digest)
for component in components:
    assert (ROOT/component['source_path']).read_bytes() == raws[component['module']]
old_owner = verify(ROOT/OVERRIDES[OWNER],baseline['sources'][OWNER])
old_audit = verify(ROOT/OVERRIDES[AUDIT],baseline['sources'][AUDIT])
assert len(old_owner) == 2744218 and raws[components[0]['module']].startswith(old_owner)
assert len(old_audit) == 436889 and audit[59:59+len(old_audit)] == old_audit
assert (ROOT/AUDIT).read_bytes() == audit and len(set(baseline['sources'])-{OWNER,AUDIT}) == 6284
assert GIT('branch','--show-current').decode().strip() == 'formalize' and GIT('rev-parse','HEAD').decode().strip() == PARENT
assert not GIT('diff','--cached','--name-only') and set(GIT('diff','--name-only','HEAD').decode().splitlines()) == {OWNER,AUDIT}
assert GIT('ls-files','--',OWNER,AUDIT).decode().splitlines() == sorted([OWNER,AUDIT]) and not GIT('ls-files','--',COLD)
assert GIT('show',PARENT+':'+OWNER) == old_owner and GIT('show',PARENT+':'+AUDIT) == old_audit
assert not GIT('ls-tree','--name-only',PARENT,'--',COLD)
# Root stages only the two existing owners and the new cold-initial leaf.
subprocess.run(['git','add','--',OWNER,AUDIT],cwd=ROOT,check=True)
ignored = subprocess.run(['git','check-ignore','--quiet','--',COLD],cwd=ROOT).returncode
assert ignored in [0,1]
subprocess.run(['git','add']+(['-f']if ignored == 0 else [])+['--',COLD],cwd=ROOT,check=True)
assert set(GIT('diff','--cached','--name-only').decode().splitlines()) == set(FILES)
for name in FILES:
    assert GIT('show',':'+name) == (ROOT/name).read_bytes()
subprocess.run(['git','diff','--cached','--check'],cwd=ROOT,check=True)
subprocess.run(['git','commit','--quiet','-m',MESSAGE],cwd=ROOT,check=True)
head = GIT('rev-parse','HEAD').decode().strip()
assert GIT('rev-parse',head+'^').decode().strip() == PARENT and set(GIT('diff-tree','--no-commit-id','--name-only','-r',head).decode().splitlines()) == set(FILES)
assert not GIT('status','--porcelain','--untracked-files=no')
for name,digest in normal.items():
    verify(ROOT/name,digest)
receipt = dict(at=datetime.datetime.now().astimezone().isoformat(),source_commit=head,parent=PARENT,files=FILES,actual_terminal=True,actual_terminal_exit=0,message=MESSAGE,publication_actual_session=verified['actual_session'],audited_theorems=report['audited_theorems'],publication_pins_independently_reverified=verified['pins_independently_reverified'],source_files=6287,audit_imports=5287,audit_reports=748,independent_reports=343,new_public_theorems=2,new_private_theorems=1,new_private_helpers_transitive=0,new_definitions=0,explicit_definition_checks=0,definition_axiom_credit=0,fresh_public_reports=2,fresh_private_reports=1,inherited_reports=560,combined_reports=563,resource_reports_inherited=264,private_actual_sessions=[private['actual_session']],rejected_private_actual_sessions=[e['actual_session']for e in stage.get('rejected_checks',[])],rejected_private_credit=0,rejected_publication_actual_sessions=[e['actual_session']for e in read(CONTROL/'rejected-publications.json')],rejected_publication_credit=0,cold_individual_pass_additive_credit=0,all_three_original_FIRSTs_exact=True,two_Shared_proof_bodies_changed=True,cold_entire_source_and_proof_exact=True,old_entire_6f681_owner_prefix_exact=False,per_qname_classification=classification['per_qname'],old_owner_bytes=2744218,old_owner_offset=0,old_Audit_bytes=436889,old_Audit_offset=59,other_old_Source_files_byte_exact=6284,force_add_used_for_new_leaf_only=ignored == 0,rebuilt_Source67_fifteen_clauses_extra_credit=0,complete_eager_worker_query_log_proved=False,joint_finite_completion_proved=False,haskell_changed=False)
(WORK/'SOURCE-COMMIT.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))
