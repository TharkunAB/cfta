from pathlib import Path
import datetime
import hashlib
import json
import re
import subprocess

ROOT = Path('/home/tritlo/Code/mcfta')
BASE = ROOT/'lean/restart-evidence'
CONTROL = BASE/'20261118-invocation-native-query-projection-source-commit-control-draft'
WORK = BASE/'20261118-invocation-native-query-projection-work'
PARENT = '1945604bc4ff5fd25e65e201ea40a492857c9247'
SOURCE_BASELINE = 'c00113a30ac80c30712a791a2cdec653c93c470a'
OLD_FILE = 'lean/MicroCFTA/Audit.lean'
NEW_FILE = 'lean/MicroCFTA/SourcePruningEnumerationInvocationNativeQueryProjection.lean'
FILES = [NEW_FILE, OLD_FILE]
MESSAGE = 'Record indexed native query origins from invocation observations'
SHA = lambda data: hashlib.sha256(data).hexdigest()
GIT = lambda *args: subprocess.check_output(['git', *args], cwd=ROOT)
assert Path(__file__).resolve().parent == WORK.resolve()
assert Path(__file__).read_bytes() == (CONTROL/'commit-source.py').read_bytes()


def verify(path, record):
    data = path.read_bytes()
    assert SHA(data) == (record['sha256'] if isinstance(record,dict) else record),str(path)
    if isinstance(record,dict) and 'bytes' in record:
        assert len(data) == record['bytes'],str(path)
    return data


def records(value):
    if isinstance(value,list):
        return [(x.get('file',x.get('path')),x) for x in value]
    return records(value['files']) if 'files' in value else value.items()


for name,record in records(json.loads((CONTROL/'MANIFEST.json').read_text())):
    verify(CONTROL/name,record)
for name,record in json.loads((CONTROL/'SOURCE-PINS.json').read_text()).items():
    verify(ROOT/name,record)
assert not (WORK/'SOURCE-COMMIT.json').exists()
stage = json.loads((WORK/'SOURCES-NORMAL-STAGING.json').read_text())
assert stage['status'] == 'SOURCE_NORMAL_STAGING_COMPLETED' and stage['normal_Source_changed']
assert set(stage['exact_Source_write_paths']) == set(FILES)
assert set(stage['baseline_overrides']) == {OLD_FILE}
assert stage['new_modules'] == 1 and stage['existing_owners_changed'] == 0
assert (stage['source_files'],stage['audit_imports'],stage['audit_reports'],stage['independent_reports']) == (6286,5286,744,339)
assert (stage['fresh_reports'],stage['inherited_reports'],stage['combined_reports']) == (1,537,538)
assert stage['new_public_theorems'] == 1 and stage['new_private_helpers_transitive'] == 0
assert stage['new_definitions'] == stage['definition_checks'] == 1
assert stage['new_Prop_definitions'] == stage['explicit_private_reports'] == 0
assert stage['resource_reports_inherited'] == 264
push = json.loads((ROOT/stage['prior_checkpoint_push_receipt']).read_text())
assert push['source_commit'] == stage['source_baseline'] == SOURCE_BASELINE
assert push['checkpoint_commit'] == push['remote_commit'] == stage['prior_checkpoint'] == PARENT
assert push['actual_push_terminal'] and push['actual_remote_check_terminal']
assert push['actual_push_terminal_exit'] == push['actual_remote_check_terminal_exit'] == push['postpush_current_tree_verifier_terminal_exit'] == 0
overrides = stage['baseline_overrides']
baseline = json.loads(verify(ROOT/stage['source_baseline_path'],stage['source_baseline_sha256']))
assert len(baseline['sources']) == 6285 and len(baseline['toolchain']) == 4
assert NEW_FILE not in baseline['sources']
assert len(set(baseline['sources'])-{OLD_FILE}) == stage['old_other_Source_files_byte_exact'] == 6284
assert {str(p.relative_to(ROOT)) for p in (ROOT/'lean/MicroCFTA').glob('*.lean')} == set(baseline['sources'])|{NEW_FILE}
for name,record in {**baseline['sources'],**baseline['toolchain']}.items():
    verify(ROOT/overrides.get(name,name),record)
normal_pins = json.loads((WORK/'NORMAL-SOURCE-PINS.json').read_text())
assert len(normal_pins) == 6290 and SHA((WORK/'NORMAL-SOURCE-PINS.json').read_bytes()) == stage['normal_source_pins_sha256']
for name,record in normal_pins.items():
    verify(ROOT/name,record)
stage_actual = json.loads((WORK/'STAGING-ACTUAL-RUN.json').read_text())
assert stage_actual['actual_terminal'] and stage_actual['actual_terminal_exit'] == 0
assert stage_actual['exact_Source_write_paths'] == stage['exact_Source_write_paths']
assert stage_actual['normal_source_pins_sha256'] == stage['normal_source_pins_sha256'] and stage_actual['git_index_empty']
assert len(stage['private_subsets']) == 1
selected = stage['private_subsets'][0]
for private_check in stage['private_subsets']+stage.get('rejected_checks',[]):
    receipt_path = private_check.get('verified_receipt',private_check.get('receipt'))
    private_receipt = json.loads((ROOT/receipt_path).read_text())
    private_actual = json.loads((ROOT/private_check['actual_receipt']).read_text())
    private_runtime = BASE/private_check['runtime']
    private_result = json.loads((private_runtime/'results.json').read_text())
    assert private_receipt['actual_session'] == private_actual['actual_session'] == private_check['actual_session']
    assert private_receipt['actual_terminal'] and private_actual['actual_terminal']
    assert private_receipt['checks'] == private_result['checks']
    if private_check in stage['private_subsets']:
        assert private_receipt['actual_terminal_exit'] == private_actual['actual_terminal_exit'] == 0
        assert private_receipt['proof_credit'] and private_result == json.loads((private_runtime/'checked.json').read_text())
        assert private_result['checks'][0]['total_axiom_reports'] == 1 and private_result['checks'][0]['declaration_checks'] == 1
    else:
        assert private_receipt['actual_terminal_exit'] == private_actual['actual_terminal_exit'] == 1
        assert not private_receipt['proof_credit'] and private_receipt['credited_public_reports'] == 0
        assert not (private_runtime/'checked.json').exists()
    private_pins = json.loads((private_runtime/'source-pins.json').read_text())
    assert SHA((private_runtime/'source-pins.json').read_bytes()) == private_receipt['source_pins_sha256']
    assert len(private_pins) == private_receipt['pins_independently_reverified'] == private_check['pins']
    for name,digest in private_pins.items():
        verify(ROOT/overrides.get(name,name),digest)
actual = json.loads((WORK/'PUBLICATION-ACTUAL-RUN.json').read_text())
verified = json.loads((WORK/'PUBLICATION-VERIFIED.json').read_text())
assert actual['actual_terminal'] and verified['actual_terminal']
assert actual['actual_terminal_exit'] == verified['actual_terminal_exit'] == 0
assert actual['actual_session'] == verified['actual_session'] and type(verified['actual_session']) is int
assert actual['runtime'] == verified['runtime'] == '20261118-invocation-native-query-projection-publication'
publication_control = BASE/'20261118-invocation-native-query-projection-publication-control-draft'
assert actual['control_manifest_sha256'] == SHA((publication_control/'MANIFEST.json').read_bytes())
assert actual['preparer_sha256'] == SHA((publication_control/'prepare-publication.py').read_bytes())
assert actual['preparer_terminal_exit'] == 0
publication = BASE/verified['runtime']
report = json.loads((publication/'checked.json').read_text())
assert report == json.loads((publication/'results.json').read_text())
assert verified['checks'] == report['checks']
assert SHA((publication/'checked.json').read_bytes()) == verified['checked_sha256']
assert SHA((publication/'source-pins.json').read_bytes()) == verified['source_pins_sha256']
assert [x['total_axiom_reports'] for x in report['checks']] == [744,1,339,744,744]
assert all(x['exit'] == 0 and not x['diagnostics'] and not x['sorryAx'] and not x['nonstandard_axioms'] for x in report['checks'])
assert report['checks'][1]['declaration_checks'] == 1
assert all(x['declaration_checks'] == 0 for x in report['checks'] if x['name'] != 'strict-new-components-and-prior-bindings')
assert report['all_five_gates_passed'] and report['source_pins_unchanged']
assert (report['fresh_reports'],report['inherited_reports'],report['combined_reports']) == (1,537,538)
assert report['new_public_theorems'] == 1 and report['new_private_theorems'] == 0
assert report['new_theorem_declarations'] == 1 and report['new_definitions'] == 1
assert report['definition_checks'] == 1 and report['definition_axiom_credit'] == 0
assert report['audited_theorems'] == verified['audited_theorems'] and type(report['audited_theorems']) is int
pub_pins = json.loads((publication/'source-pins.json').read_text())
assert len(pub_pins) == verified['pins_independently_reverified']
for name,record in pub_pins.items():
    verify(ROOT/name,record)
assert len(stage['components']) == 1
component = stage['components'][0]
packet = BASE/component['packet']
verify(packet/'MANIFEST.json',component['manifest_sha256'])
for name,record in records(json.loads((packet/'MANIFEST.json').read_text())):
    verify(packet/name,record)
current = verify(ROOT/NEW_FILE,{'bytes':component['raw_bytes'],'sha256':component['raw_sha256']})
assert current == (packet/component['source']).read_bytes()
for header_name,header_sha256 in component['headers'].items():
    data = verify(packet/header_name,header_sha256).rstrip()
    assert current.count(data) == 1
    tail = current[current.index(data)+len(data):]
    assert re.match(rb'\s*:=',tail)
    if not re.match(rb'(?:noncomputable\s+)?def\s',data.lstrip()):
        assert re.match(rb'\s*:= by',tail)
old_audit = verify(ROOT/overrides[OLD_FILE],{'bytes':436549,'sha256':stage['old_audit_sha256']})
imports = (WORK/'IMPORTS.lean.txt').read_bytes()
probes = (WORK/'PUBLIC-PROBES.lean.txt').read_bytes()
assert imports == b'import MicroCFTA.SourcePruningEnumerationInvocationNativeQueryProjection\n' and len(imports) == 73
assert (ROOT/OLD_FILE).read_bytes() == imports+old_audit+b'\n'+probes
assert len((ROOT/OLD_FILE).read_bytes()) == stage['staged_audit_bytes'] == 436723
assert len(re.findall(rb'^#print axioms ',probes,re.M)) == 1 and b'#check ' not in probes
assert GIT('branch','--show-current').decode().strip() == 'formalize'
assert GIT('rev-parse','HEAD').decode().strip() == PARENT
assert not GIT('diff','--cached','--name-only')
assert set(GIT('diff','--name-only','HEAD').decode().splitlines()) == {OLD_FILE}
assert GIT('ls-files','--',OLD_FILE).decode().splitlines() == [OLD_FILE]
assert not GIT('ls-files','--',NEW_FILE)
assert GIT('show',PARENT+':'+OLD_FILE) == old_audit
source_bytes = {n:(ROOT/n).read_bytes() for n in FILES}
# Root stages only these paths. Force-add the new path only when it is ignored.
ignored = subprocess.run(['git','check-ignore','-q','--',NEW_FILE],cwd=ROOT).returncode
assert ignored in [0,1]
subprocess.run(['git','add','--',OLD_FILE],cwd=ROOT,check=True)
subprocess.run(['git','add']+(['-f'] if ignored == 0 else [])+['--',NEW_FILE],cwd=ROOT,check=True)
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
    source_files=6286,audit_imports=5286,audit_reports=744,independent_reports=339,fresh_public_reports=1,
    inherited_reports=537,combined_reports=538,new_public_theorems=1,new_private_theorems=0,new_definitions=1,
    explicit_definition_checks=1,definition_axiom_credit=0,resource_reports_inherited=264,
    private_actual_session=selected['actual_session'],rejected_private_actual_sessions=[x['actual_session'] for x in stage.get('rejected_checks',[])],rejected_private_credit=0,
    selected_private_control_manifest=selected['control_manifest_sha256'],all_definition_and_origin_FIRST_headers_checked=True,
    old_audit_bytes=436549,old_audit_offset=73,force_add_used=ignored==0,
    redundant_endpoint_extra_credit=0,all_original_eager_worker_query_admissions_proved=False,
    original_eager_worker_all_calls_Seeds_propagation_proved=False,joint_finite_completion_proved=False,haskell_changed=False)
(WORK/'SOURCE-COMMIT.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))
