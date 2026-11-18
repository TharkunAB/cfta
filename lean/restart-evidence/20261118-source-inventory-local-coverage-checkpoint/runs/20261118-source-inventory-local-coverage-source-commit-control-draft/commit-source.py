from pathlib import Path
import datetime
import hashlib
import json
import subprocess
ROOT = Path('/home/tritlo/Code/mcfta')
BASE = ROOT/'lean/restart-evidence'
CONTROL = BASE/'20261118-source-inventory-local-coverage-source-commit-control-draft'
PUBLICATION_CONTROL = BASE/'20261118-source-inventory-local-coverage-publication-control-draft'
WORK = BASE/'20261118-source-inventory-local-coverage-work'
RUNTIME = BASE/'20261118-source-inventory-local-coverage-publication'
PARENT = 'f253502aa327b3a2c5b47da81e33a075e2032c84'
OWNER = 'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'
NEW_LEAVES = ['lean/MicroCFTA/SourceCurrentClosedRecursiveBoundaryMuOrigin.lean','lean/MicroCFTA/SourceSynthesisCurrentDoneOutputAssignmentInventory.lean']
AUDIT = 'lean/MicroCFTA/Audit.lean'
FILES = [OWNER,*NEW_LEAVES,AUDIT]
MESSAGE = 'Expose source inventory assignments and local query coverage laws'
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
verified,actual = read(WORK/'PUBLICATION-VERIFIED.json'),read(WORK/'PUBLICATION-ACTUAL-RUN.json')
assert verified['actual_terminal'] and actual['actual_terminal'] and verified['actual_terminal_exit'] == actual['actual_terminal_exit'] == 0
assert type(verified['actual_session']) is int and verified['actual_session'] == actual['actual_session']
assert verified['runtime'] == actual['runtime'] == RUNTIME.name
assert actual['control_manifest_sha256'] == SHA((PUBLICATION_CONTROL/'MANIFEST.json').read_bytes())
assert actual['preparer_sha256'] == SHA((PUBLICATION_CONTROL/'prepare-publication.py').read_bytes()) and actual['preparer_terminal_exit'] == 0
report = json.loads(verify(RUNTIME/'checked.json',verified['checked_sha256']))
assert report == json.loads(verify(RUNTIME/'results.json',verified['results_sha256'])) and report['checks'] == verified['checks']
assert report['all_five_gates_passed'] and report['source_pins_unchanged']
assert [e['total_axiom_reports']for e in report['checks']] == [751,4,346,751,751]
assert all(e['exit'] == 0 and not e['diagnostics'] and not e['sorryAx'] and not e['nonstandard_axioms'] for e in report['checks'])
assert [e['declaration_checks'] for e in report['checks']] == [0,0,0,0,0]
assert report['checks'][1]['axiom_groups'] == classification['axiom_groups'] and report['checks'][1]['axiom_free_reports'] == classification['axiom_free_reports']
assert (report['fresh_public_reports'],report['fresh_private_reports'],report['inherited_reports'],report['combined_reports']) == (2,2,564,568)
assert report['new_definitions'] == report['definition_checks'] == 0 and report['definition_axiom_credit'] == report['new_private_helpers_transitive'] == 0
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
assert len(normal) == 6294 and len(list((ROOT/'lean/MicroCFTA').glob('*.lean'))) == 6290
for name,digest in normal.items():
    verify(ROOT/name,digest)
for component in components:
    assert (ROOT/component['source_path']).read_bytes() == raws[component['module']]
old_owner = verify(ROOT/OVERRIDES[OWNER],baseline['sources'][OWNER])
old_audit = verify(ROOT/OVERRIDES[AUDIT],baseline['sources'][AUDIT])
owner_component = components[0]
owner_packet = BASE/owner_component['packet']
owner_imports = verify(owner_packet/owner_component['imports'],owner_component['imports_raw'])
owner_append = verify(owner_packet/owner_component['append'],owner_component['append_raw'])
assert len(owner_imports) == owner_component['old_owner_offset'] == 73
assert len(old_owner) == 2842768 and raws[owner_component['module']] == owner_imports+old_owner+owner_append
assert raws[owner_component['module']][73:73+2842768] == old_owner
assert len(old_audit) == 437344 and audit[131:131+len(old_audit)] == old_audit
assert (ROOT/AUDIT).read_bytes() == audit and len(set(baseline['sources'])-{OWNER,AUDIT}) == 6286
assert GIT('branch','--show-current').decode().strip() == 'formalize' and GIT('rev-parse','HEAD').decode().strip() == PARENT
assert not GIT('diff','--cached','--name-only') and set(GIT('diff','--name-only','HEAD').decode().splitlines()) == {OWNER,AUDIT}
assert GIT('ls-files','--',OWNER,AUDIT).decode().splitlines() == sorted([OWNER,AUDIT])
assert GIT('show',PARENT+':'+OWNER) == old_owner and GIT('show',PARENT+':'+AUDIT) == old_audit
for name in NEW_LEAVES:
    assert not GIT('ls-files','--',name) and not GIT('ls-tree','--name-only',PARENT,'--',name)
# Root stages only Shared, Audit and the two new public leaves.
subprocess.run(['git','add','--',OWNER,AUDIT],cwd=ROOT,check=True)
force_added = []
for name in NEW_LEAVES:
    ignored = subprocess.run(['git','check-ignore','--quiet','--',name],cwd=ROOT).returncode
    assert ignored in [0,1]
    subprocess.run(['git','add']+(['-f']if ignored == 0 else [])+['--',name],cwd=ROOT,check=True)
    if ignored == 0:
        force_added.append(name)
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
receipt = dict(at=datetime.datetime.now().astimezone().isoformat(),source_commit=head,parent=PARENT,files=FILES,actual_terminal=True,actual_terminal_exit=0,message=MESSAGE,publication_actual_session=verified['actual_session'],audited_theorems=report['audited_theorems'],publication_pins_independently_reverified=verified['pins_independently_reverified'],source_files=6290,audit_imports=5290,audit_reports=751,independent_reports=346,new_public_theorems=2,new_private_theorems=2,new_private_helpers_transitive=0,new_definitions=0,new_constructors=0,explicit_definition_checks=0,definition_axiom_credit=0,fresh_public_reports=2,fresh_private_reports=2,inherited_reports=564,combined_reports=568,resource_reports_inherited=264,private_actual_sessions=[private['actual_session']],rejected_private_actual_sessions=[e['actual_session']for e in stage.get('rejected_checks',[])],rejected_private_credit=0,rejected_publication_actual_sessions=[e['actual_session']for e in read(CONTROL/'rejected-publications.json')],rejected_publication_credit=0,all_four_original_FIRSTs_exact=True,all_four_original_proof_bodies_exact=False,two_public_sources_and_proofs_exact=True,fallback_proof_exact=True,lower_proof_explicit_equality_type_changed=True,per_qname_classification=classification['per_qname'],old_owner_bytes=2842768,old_owner_offset=73,Shared_import_prefix_bytes=73,old_Audit_bytes=437344,old_Audit_offset=131,other_old_Source_files_byte_exact=6286,force_added_new_module_paths=force_added,rebuilt_Source69_relations_and_36_constructors_extra_credit=0,rebuilt_Source69_generated_brecOn_extra_credit=0,old_generic_Mu_actual22743_additive_credit=0,coverage_producer_implemented=False,complete_eager_worker_query_log_proved=False,joint_finite_completion_proved=False,haskell_changed=False)
(WORK/'SOURCE-COMMIT.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))
