from pathlib import Path
import datetime
import hashlib
import json
import subprocess
ROOT = Path('/home/tritlo/Code/mcfta')
BASE = ROOT/'lean/restart-evidence'
CONTROL = BASE/'20261118-no-mu-native-inventory-source-commit-control-draft'
PUBLICATION_CONTROL = BASE/'20261118-no-mu-native-inventory-publication-control-draft'
WORK = BASE/'20261118-no-mu-native-inventory-work'
RUNTIME = BASE/'20261118-no-mu-native-inventory-publication'
PARENT = 'ef5cd82556c4edc671fcbecd8197ae222b11f3b1'
LEAF = 'lean/MicroCFTA/SourceCurrentNativeNoMuInventory.lean'
AUDIT = 'lean/MicroCFTA/Audit.lean'
FILES = [LEAF,AUDIT]
MESSAGE = 'Preserve native request inventory for no-Mu inputs'
SHA = lambda data: hashlib.sha256(data).hexdigest()
read = lambda path: json.loads(path.read_text())
git = lambda *args: subprocess.check_output(['git',*args],cwd=ROOT)
assert (CONTROL/'STATUS.txt').read_text().startswith('FROZEN'),'OPEN control; do not execute.'
assert Path(__file__).resolve().parent == WORK and Path(__file__).read_bytes() == (CONTROL/'commit-source.py').read_bytes()
assert read(CONTROL/'MANIFEST.json')['all_final_receipts_bound_before_freeze']
assert not (WORK/'SOURCE-COMMIT.json').exists()
stage = read(WORK/'SOURCES-NORMAL-STAGING.json')
OVERRIDES = stage['baseline_overrides']
exec(compile((PUBLICATION_CONTROL/'validate-inputs.py.txt').read_text(),str(PUBLICATION_CONTROL/'validate-inputs.py.txt'),'exec'))
packet(CONTROL)
for name,record in records(read(CONTROL/'SOURCE-PINS.json')):
    verify(ROOT/name,record)
stage,baseline,component,raw,probe,audit,private,prior,classification = preflight(PUBLICATION_CONTROL)
assert stage['status'] == 'SOURCE_NORMAL_STAGING_COMPLETED' and set(stage['exact_Source_write_paths']) == set(FILES)
verified,actual = read(WORK/'PUBLICATION-VERIFIED.json'),read(WORK/'PUBLICATION-ACTUAL-RUN.json')
assert verified['actual_terminal'] and actual['actual_terminal'] and verified['actual_terminal_exit'] == actual['actual_terminal_exit'] == 0
assert verified['actual_session'] == actual['actual_session'] and verified['runtime'] == actual['runtime'] == RUNTIME.name
assert actual['control_manifest_sha256'] == SHA((PUBLICATION_CONTROL/'MANIFEST.json').read_bytes())
assert actual['preparer_sha256'] == SHA((PUBLICATION_CONTROL/'prepare-publication.py').read_bytes()) and actual['preparer_terminal_exit'] == 0
report = json.loads(verify(RUNTIME/'checked.json',verified['checked_sha256']))
assert report == json.loads(verify(RUNTIME/'results.json',verified['results_sha256'])) and report['checks'] == verified['checks']
assert report['all_five_gates_passed'] and report['source_pins_unchanged']
assert [e['total_axiom_reports'] for e in report['checks']] == [752,1,347,752,752]
assert [e['declaration_checks'] for e in report['checks']] == [0,0,0,0,0]
assert all(e['exit'] == 0 and not e['diagnostics'] and not e['sorryAx'] and not e['nonstandard_axioms'] for e in report['checks'])
assert report['checks'][1]['axiom_groups'] == classification['axiom_groups'] and report['checks'][1]['axiom_free_reports'] == classification['axiom_free_reports']
assert (report['fresh_public_reports'],report['fresh_private_reports'],report['inherited_reports'],report['combined_reports']) == (1,0,568,569)
assert report['audited_theorems'] == verified['audited_theorems'] and type(report['audited_theorems']) is int
pins_map = json.loads(verify(RUNTIME/'source-pins.json',verified['source_pins_sha256']))
assert len(pins_map) == verified['pins_independently_reverified']
for name,digest in pins_map.items():
    verify(ROOT/name,digest)
normal = json.loads(verify(WORK/'NORMAL-SOURCE-PINS.json',stage['normal_source_pins_sha256']))
assert len(normal) == 6295 and len(list((ROOT/'lean/MicroCFTA').glob('*.lean'))) == 6291
for name,digest in normal.items():
    verify(ROOT/name,digest)
assert (ROOT/LEAF).read_bytes() == raw and (ROOT/AUDIT).read_bytes() == audit
assert git('branch','--show-current').decode().strip() == 'formalize' and git('rev-parse','HEAD').decode().strip() == PARENT
assert not git('diff','--cached','--name-only') and git('diff','--name-only','HEAD').decode().splitlines() == [AUDIT]
assert git('ls-files','--',AUDIT).decode().splitlines() == [AUDIT] and not git('ls-files','--',LEAF)
assert not git('ls-tree','--name-only',PARENT,'--',LEAF)
assert git('show',PARENT+':'+AUDIT) == (ROOT/OVERRIDES[AUDIT]).read_bytes()
# Root stages only Audit and the new public leaf.
subprocess.run(['git','add','--',AUDIT],cwd=ROOT,check=True)
ignored = subprocess.run(['git','check-ignore','--quiet','--',LEAF],cwd=ROOT).returncode
assert ignored in [0,1]
subprocess.run(['git','add']+(['-f'] if ignored == 0 else [])+['--',LEAF],cwd=ROOT,check=True)
assert set(git('diff','--cached','--name-only').decode().splitlines()) == set(FILES)
for name in FILES:
    assert git('show',':'+name) == (ROOT/name).read_bytes()
subprocess.run(['git','diff','--cached','--check'],cwd=ROOT,check=True)
subprocess.run(['git','commit','--quiet','-m',MESSAGE],cwd=ROOT,check=True)
head = git('rev-parse','HEAD').decode().strip()
assert git('rev-parse',head+'^').decode().strip() == PARENT and set(git('diff-tree','--no-commit-id','--name-only','-r',head).decode().splitlines()) == set(FILES)
assert not git('status','--porcelain','--untracked-files=no')
for name,digest in normal.items():
    verify(ROOT/name,digest)
receipt = dict(at=datetime.datetime.now().astimezone().isoformat(),source_commit=head,parent=PARENT,files=FILES,actual_terminal=True,actual_terminal_exit=0,message=MESSAGE,publication_actual_session=verified['actual_session'],audited_theorems=report['audited_theorems'],publication_pins_independently_reverified=verified['pins_independently_reverified'],source_files=6291,audit_imports=5291,audit_reports=752,independent_reports=347,new_public_theorems=1,new_private_theorems=0,new_private_helpers_transitive=0,new_definitions=0,definition_axiom_credit=0,fresh_public_reports=1,fresh_private_reports=0,inherited_reports=568,combined_reports=569,resource_reports_inherited=264,private_actual_sessions=[private['actual_session']],FIRST_and_proof_exact=True,per_qname_classification=classification['per_qname'],old_Audit_bytes=437705,old_Audit_offset=50,other_old_Source_files_byte_exact=6289,force_add_used_for_new_leaf_only=ignored == 0,no_mu_worker_inventory_attachment_proved=False,full_coverage_producer334c_proved=False,joint_finite_completion_proved=False,haskell_changed=False)
(WORK/'SOURCE-COMMIT.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))
